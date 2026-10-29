import BstLean.Part269TailBounds
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
import BstLean.Part269Direction6
import BstLean.Part269Shared6
import BstLean.Part269Finite
import BstLean.Part269Rows6
import BstLean.Part269Source
/-! Actual 12500 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12500 ≤ (1.036097087640 : ℝ) := by
  have hr : (111.803398874989 : ℝ) ≤ √(12500 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.803398874989 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12500 12500 (11 / 1000) ≤
    (0.008549714030 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12500) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.803398874989 : ℝ) ≤ √(12500 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12500)
  have hdiv : K / √(12500 : ℝ) ≤ K / 111.803398874989 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.803398874989 ≤ (0.008549714030 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12500.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12500 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12500 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12500 := gPlus_lower 12500
end BstLean.Part269.N12500

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12500
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036097087639 : ℝ) ≤ wn 12500 := by
  have hn : √(12500 : ℝ) ≤ 111.803398874990 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12500 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.803398874990 ≤ 2 / √(12500 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255982084 : ℝ) ≤ rhoBar 12500 BstLean.Part154.csC ∧
    rhoBar 12500 BstLean.Part154.csC ≤ 0.000255982481 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036097087639 : ℝ) / (1.295212 * 12500) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036097087640 : ℝ) / (1.29521 * 12500) := by gcongr
      _ ≤ (0.000255982481 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12500 BstLean.Part154.csC) ≤ 0.001023995452 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12500 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) ≤ 0.000195521294 ∧
    cc1 (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) ≤ 0.000124411467 ∧
    cc2 (rhoBar 12500 BstLean.Part154.csC) ≤ 0.000072221773 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12500 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12500 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12500 BstLean.Part154.csC * nuR (rhoBar 12500 BstLean.Part154.csC)) ≤ 0.000511981344 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255982481 : ℝ) * 0.001023995452 := by gcongr
      _ ≤ (0.000511981344 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12500 BstLean.Part154.csC) * nuR (rhoBar 12500 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023995452 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12500 BstLean.Part154.csC) * rhoBar 12500 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255982481 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255982481 / 2 + 0.399 * 0.001023995452 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195521294 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511981344 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124411467 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255982481 / 1.414213562 := by gcongr
      _ ≤ (0.000072221773 : ℝ) := by norm_num

end BstLean.Part269.N12500

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12500
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) ≤ 1.65091E-7 := by
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12500 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12500 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12500 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195521294 : ℝ) ^ 2 + 0.000124411467 ^ 2 + 3 * 0.000072221773 ^ 2 +
        2 * 0.797885 * 0.000195521294 * 0.000124411467 + 2 * 0.000195521294 * 0.000072221773 +
        4 * 0.797885 * 0.000124411467 * 0.000072221773 := by gcongr
    _ ≤ (1.65091E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12500 BstLean.Part154.csC Θ ≤ 0.002672848063 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12500 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12500 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12500 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036097087640 * 1.65091E-7 / (0.000255982084 : ℝ) := by gcongr
    _ ≤ 0.002672848063 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12500 BstLean.Part154.csC Θ ≤ 0.002966490389 + 0.000675384208 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12500 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12500 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036097087640 : ℝ) * ((2 * Θ * 0.000255982481 +
        (6863 / 10000) * 0.000255982481 * 12500 * 0.001023995452) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002966490389 + 0.000675384208 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12500 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12500 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12500 0.011 Θ ∧ gammaRatio 12500 0.011 Θ ≤ 0.000088000158 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12500 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036097087640 : ℝ) * 0.525 / ((1 - 0.011) * 12500) := by gcongr
      _ ≤ (0.000088000158 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12500 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12500 0.011 Θ) :=
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
    badAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12500 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12500 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12500 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12500 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12500 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12500 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12500 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12500 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12500 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12500 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036097087640 : ℝ) * 12500 *
        (3.0670E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003740909217 + 0.003348232271 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12500

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12500
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12500 BstLean.Part154.csC) (piBar (rhoBar 12500 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12500 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12500 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12500 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12500 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12500 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12500 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12500 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12500 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12500 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12500 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052907092068 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12500) ≤ 0.010681585651 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12500 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036097087640)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010681585651 + 2 * 0.737676 / 12500) := by gcongr
    _ ≤ (0.052907092068 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12500 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12500

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12500
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494378984 : ℝ) ≤ plow 12500 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12500) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053005331160)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403245234) : eMP 12500 0.011 xi bn ≤ 0.001207784051 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12500 : ℝ) * (1 - 0.011))) ≤ 0.000597157094 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403245234 / (12500 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597157094 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597157094 : ℝ) + 3.141593 * 0.053005331160 / (12500 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207784051 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053005331160)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403245234) : PiBarMP 12500 12 0.011 xi bn ≤ 0.162549126068 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12500 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037459915030 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.186779789685 : ℝ) ≤ √((12500 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.803398874989 : ℝ) ≤ √(12500 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12500) ≤ 0.124615247864 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037459915030 + 0.053005331160 * 1.772454 / (2 * (111.186779789685 : ℝ))) * (1 + 0.001207784051) +
        8 / (12500 * 111.803398874989) + 0.124615247864 := by gcongr
    _ ≤ (0.162549126068 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053005331160)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403245234) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283135958981) :
    parallelOracle 12500 0.011 xi bn cd ≤ 0.163555980918 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12500 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12500 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494378984 : ℝ) ≤ plow 12500 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.803398874989 : ℝ) ≤ √(12500 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283135958981 : ℝ) / (2 * 0.560494378984 * 111.803398874989)) * 0.162549126068 +
        0.283135958981 ^ 2 / (2 * 0.560494378984 * 111.803398874989) := by gcongr
    _ ≤ (0.163555980918 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053005331160) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403245234)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283135958981) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12500 12500 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494378984 : ℝ) ≤ plow 12500 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.803398874989 : ℝ) ≤ √(12500 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12500 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12500 Θ 1.22 ≤ 0.011861003452 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.803398874989 := by gcongr <;> linarith
      _ ≤ (0.011861003452 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12500 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12500 12500 0.011 ≤ 0.008549714030 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12500 12500 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12500 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12500 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12500 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12500 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163555980918 + 0.011861003452 + (0.008549714030 : ℝ) *
        (1 + 2 * (0.283135958981 + 0.011861003452) / (0.560494378984 * 111.803398874989))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12500]

end BstLean.Part269.N12500

/-! The original eight local profiles supply actual 12500 moment certificates. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12500 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053005331160 ∧
    0 ≤ bN 12500 BstLean.Part154.csC (groupTheta g) ∧ bN 12500 BstLean.Part154.csC (groupTheta g) ≤ 0.001403245234 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12500 12500 0.011
      (momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12500 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12500 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12500 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230228866913 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12500 0.011
      (momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12500 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12500
/-! The actual computed-centre upper energy formula at 12500. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12500

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12500)
open BstLean.Part268 (cell12500)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086096757606
  | 2 => 0.087051194846
  | 3 => 0.088005563124
  | 4 => 0.088961686580
  | 5 => 0.089921757050
  | 6 => 0.090888386760
  | 7 => 0.091864665613
  | 8 => 0.092854223080
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12500 12500 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12500 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12500

/-! Actual upper energy certificates on all 43 source endpoints at 12500. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12500)
open BstLean.Part268 (cell12500)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12500 (gMinus 12500) (1 - (cell12500 i).lower) ≤ 1 ∧
    energyUpper 12500 (gMinus 12500) (BstLean.Part211.gPlus 12500)
      (finiteEnergy 12500 12500 0.011) (1 - (cell12500 i).lower) ≤
      (cell12500 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨10,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨11,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨12,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨13,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨14,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨15,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨16,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨17,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨18,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨19,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨20,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨21,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨22,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨23,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨24,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨25,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨26,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨27,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨28,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨29,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨30,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨31,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨32,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨33,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨34,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨35,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨36,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨37,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨38,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨39,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨40,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨41,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨42,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨43,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨44,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨45,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨46,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨47,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨48,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨49,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨50,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨51,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12500) (by norm_num)
        (q := 1 - (cell12500 ⟨52,by decide⟩).lower)
        (by norm_num [cell12500]) (by norm_num [cell12500])
      exact ⟨E.1,E.2.trans (by norm_num [cell12500])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12500

/-! Source-cell containment and simple scalar guards at 12500. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12500)
open BstLean.Part268 (cell12500)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12500 ⟨10,by decide⟩).lower ∧ (cell12500 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12500 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12500 ⟨11,by decide⟩).lower ∧ (cell12500 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12500 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12500 ⟨12,by decide⟩).lower ∧ (cell12500 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12500 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12500 ⟨13,by decide⟩).lower ∧ (cell12500 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12500 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12500 ⟨14,by decide⟩).lower ∧ (cell12500 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12500 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12500 ⟨15,by decide⟩).lower ∧ (cell12500 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12500 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12500 ⟨16,by decide⟩).lower ∧ (cell12500 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12500 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12500 ⟨17,by decide⟩).lower ∧ (cell12500 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12500 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12500 ⟨18,by decide⟩).lower ∧ (cell12500 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12500 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12500 ⟨19,by decide⟩).lower ∧ (cell12500 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12500 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12500 ⟨20,by decide⟩).lower ∧ (cell12500 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12500 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12500 ⟨21,by decide⟩).lower ∧ (cell12500 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12500 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12500 ⟨22,by decide⟩).lower ∧ (cell12500 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12500 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12500 ⟨23,by decide⟩).lower ∧ (cell12500 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12500 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12500 ⟨24,by decide⟩).lower ∧ (cell12500 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12500 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12500 ⟨25,by decide⟩).lower ∧ (cell12500 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12500 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12500 ⟨26,by decide⟩).lower ∧ (cell12500 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12500 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12500 ⟨27,by decide⟩).lower ∧ (cell12500 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12500 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12500 ⟨28,by decide⟩).lower ∧ (cell12500 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12500 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12500 ⟨29,by decide⟩).lower ∧ (cell12500 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12500 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12500 ⟨30,by decide⟩).lower ∧ (cell12500 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12500 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12500 ⟨31,by decide⟩).lower ∧ (cell12500 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12500 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12500 ⟨32,by decide⟩).lower ∧ (cell12500 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12500 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12500 ⟨33,by decide⟩).lower ∧ (cell12500 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12500 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12500 ⟨34,by decide⟩).lower ∧ (cell12500 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12500 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12500 ⟨35,by decide⟩).lower ∧ (cell12500 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12500 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12500 ⟨36,by decide⟩).lower ∧ (cell12500 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12500 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12500 ⟨37,by decide⟩).lower ∧ (cell12500 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12500 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12500 ⟨38,by decide⟩).lower ∧ (cell12500 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12500 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12500 ⟨39,by decide⟩).lower ∧ (cell12500 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12500 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12500 ⟨40,by decide⟩).lower ∧ (cell12500 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12500 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12500 ⟨41,by decide⟩).lower ∧ (cell12500 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12500 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12500 ⟨42,by decide⟩).lower ∧ (cell12500 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12500 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12500 ⟨43,by decide⟩).lower ∧ (cell12500 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12500 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12500 ⟨44,by decide⟩).lower ∧ (cell12500 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12500 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12500 ⟨45,by decide⟩).lower ∧ (cell12500 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12500 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12500 ⟨46,by decide⟩).lower ∧ (cell12500 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12500 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12500 ⟨47,by decide⟩).lower ∧ (cell12500 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12500 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12500 ⟨48,by decide⟩).lower ∧ (cell12500 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12500 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12500 ⟨49,by decide⟩).lower ∧ (cell12500 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12500 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12500 ⟨50,by decide⟩).lower ∧ (cell12500 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12500 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12500 ⟨51,by decide⟩).lower ∧ (cell12500 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12500 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12500 ⟨52,by decide⟩).lower ∧ (cell12500 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12500 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12500 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12500 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12500,cell12500,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12500 i).lower ∧
    (cell12500 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12500 i).upper ≤ (0.532 : ℝ) ∧
    (cell12500 i).centre ≤ (0.1 : ℝ) ∧ (cell12500 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12500 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12500 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12500

/-! The local source numeric instances at 12500 have no network premises. -/
namespace BstLean.Part269.N12500
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12500)
open BstLean.Part268 (cell12500)

noncomputable def sourceNumerics12500 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12500 (cell12500 i)
      scalarRow12500.M scalarRow12500.H scalarRow12500.xi := by
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
    energy_allowance := scalarRow12500.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12500]
    centre_nonneg := (scalarRow12500.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12500])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12500
/-! Actual 12501 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12501 ≤ (1.036095631045 : ℝ) := by
  have hr : (111.807870921505 : ℝ) ≤ √(12501 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.807870921505 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12501 12501 (11 / 1000) ≤
    (0.008549372059 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12501) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.807870921505 : ℝ) ≤ √(12501 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12501)
  have hdiv : K / √(12501 : ℝ) ≤ K / 111.807870921505 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.807870921505 ≤ (0.008549372059 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12501.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12501 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12501 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12501 := gPlus_lower 12501
end BstLean.Part269.N12501

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12501
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036095631044 : ℝ) ≤ wn 12501 := by
  have hn : √(12501 : ℝ) ≤ 111.807870921506 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12501 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.807870921506 ≤ 2 / √(12501 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255961248 : ℝ) ≤ rhoBar 12501 BstLean.Part154.csC ∧
    rhoBar 12501 BstLean.Part154.csC ≤ 0.000255961644 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036095631044 : ℝ) / (1.295212 * 12501) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036095631045 : ℝ) / (1.29521 * 12501) := by gcongr
      _ ≤ (0.000255961644 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12501 BstLean.Part154.csC) ≤ 0.001023912093 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12501 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) ≤ 0.000195505378 ∧
    cc1 (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) ≤ 0.000124401340 ∧
    cc2 (rhoBar 12501 BstLean.Part154.csC) ≤ 0.000072215894 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12501 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12501 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12501 BstLean.Part154.csC * nuR (rhoBar 12501 BstLean.Part154.csC)) ≤ 0.000511939667 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255961644 : ℝ) * 0.001023912093 := by gcongr
      _ ≤ (0.000511939667 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12501 BstLean.Part154.csC) * nuR (rhoBar 12501 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023912093 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12501 BstLean.Part154.csC) * rhoBar 12501 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255961644 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255961644 / 2 + 0.399 * 0.001023912093 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195505378 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511939667 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124401340 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255961644 / 1.414213562 := by gcongr
      _ ≤ (0.000072215894 : ℝ) := by norm_num

end BstLean.Part269.N12501

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12501
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) ≤ 1.65064E-7 := by
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12501 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12501 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12501 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195505378 : ℝ) ^ 2 + 0.000124401340 ^ 2 + 3 * 0.000072215894 ^ 2 +
        2 * 0.797885 * 0.000195505378 * 0.000124401340 + 2 * 0.000195505378 * 0.000072215894 +
        4 * 0.797885 * 0.000124401340 * 0.000072215894 := by gcongr
    _ ≤ (1.65064E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12501 BstLean.Part154.csC Θ ≤ 0.002672624713 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12501 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12501 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12501 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036095631045 * 1.65064E-7 / (0.000255961248 : ℝ) := by gcongr
    _ ≤ 0.002672624713 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12501 BstLean.Part154.csC Θ ≤ 0.002966240558 + 0.000675328283 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12501 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12501 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036095631045 : ℝ) * ((2 * Θ * 0.000255961644 +
        (6863 / 10000) * 0.000255961644 * 12501 * 0.001023912093) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002966240558 + 0.000675328283 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12501 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12501 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12501 0.011 Θ ∧ gammaRatio 12501 0.011 Θ ≤ 0.000087992994 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12501 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036095631045 : ℝ) * 0.525 / ((1 - 0.011) * 12501) := by gcongr
      _ ≤ (0.000087992994 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12501 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12501 0.011 Θ) :=
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
    badAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12501 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12501 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12501 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12501 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12501 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12501 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12501 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12501 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12501 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12501 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036095631045 : ℝ) * 12501 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003740659386 + 0.003347952996 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12501

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12501
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12501 BstLean.Part154.csC) (piBar (rhoBar 12501 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12501 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12501 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12501 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12501 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12501 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12501 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12501 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12501 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12501 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12501 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052904952784 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12501) ≤ 0.010681158413 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12501 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036095631045)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010681158413 + 2 * 0.737676 / 12501) := by gcongr
    _ ≤ (0.052904952784 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12501 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12501

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12501
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494425661 : ℝ) ≤ plow 12501 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12501) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004934709)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403127975) : eMP 12501 0.011 xi bn ≤ 0.001207685205 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12501 : ℝ) * (1 - 0.011))) ≤ 0.000597108260 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403127975 / (12501 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597108260 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597108260 : ℝ) + 3.141593 * 0.053004934709 / (12501 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207685205 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004934709)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403127975) : PiBarMP 12501 12 0.011 xi bn ≤ 0.162542550194 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12501 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037458349871 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.191227171931 : ℝ) ≤ √((12501 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.807870921505 : ℝ) ≤ √(12501 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12501) ≤ 0.124610263553 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037458349871 + 0.053004934709 * 1.772454 / (2 * (111.191227171931 : ℝ))) * (1 + 0.001207685205) +
        8 / (12501 * 111.807870921505) + 0.124610263553 := by gcongr
    _ ≤ (0.162542550194 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004934709)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403127975) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283132958703) :
    parallelOracle 12501 0.011 xi bn cd ≤ 0.163549332387 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12501 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12501 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494425661 : ℝ) ≤ plow 12501 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.807870921505 : ℝ) ≤ √(12501 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283132958703 : ℝ) / (2 * 0.560494425661 * 111.807870921505)) * 0.162542550194 +
        0.283132958703 ^ 2 / (2 * 0.560494425661 * 111.807870921505) := by gcongr
    _ ≤ (0.163549332387 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004934709) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403127975)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283132958703) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12501 12501 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494425661 : ℝ) ≤ plow 12501 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.807870921505 : ℝ) ≤ √(12501 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12501 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12501 Θ 1.22 ≤ 0.011860529041 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.807870921505 := by gcongr <;> linarith
      _ ≤ (0.011860529041 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12501 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12501 12501 0.011 ≤ 0.008549372059 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12501 12501 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12501 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12501 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12501 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12501 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163549332387 + 0.011860529041 + (0.008549372059 : ℝ) *
        (1 + 2 * (0.283132958703 + 0.011860529041) / (0.560494425661 * 111.807870921505))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12501]

end BstLean.Part269.N12501

/-! The original eight local profiles supply actual 12501 moment certificates. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12501 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053004934709 ∧
    0 ≤ bN 12501 BstLean.Part154.csC (groupTheta g) ∧ bN 12501 BstLean.Part154.csC (groupTheta g) ≤ 0.001403127975 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12501 12501 0.011
      (momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12501 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12501 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12501 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230228005919 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12501 0.011
      (momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12501 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12501
/-! The actual computed-centre upper energy formula at 12501. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12501

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12501)
open BstLean.Part268 (cell12501)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086093601209
  | 2 => 0.087047974735
  | 3 => 0.088002269108
  | 4 => 0.088958306187
  | 5 => 0.089918275146
  | 6 => 0.090884785104
  | 7 => 0.091860922382
  | 8 => 0.092850312329
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12501 12501 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12501 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12501

/-! Actual upper energy certificates on all 43 source endpoints at 12501. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12501)
open BstLean.Part268 (cell12501)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12501 (gMinus 12501) (1 - (cell12501 i).lower) ≤ 1 ∧
    energyUpper 12501 (gMinus 12501) (BstLean.Part211.gPlus 12501)
      (finiteEnergy 12501 12501 0.011) (1 - (cell12501 i).lower) ≤
      (cell12501 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨10,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨11,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨12,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨13,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨14,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨15,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨16,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨17,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨18,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨19,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨20,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨21,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨22,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨23,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨24,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨25,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨26,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨27,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨28,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨29,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨30,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨31,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨32,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨33,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨34,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨35,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨36,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨37,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨38,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨39,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨40,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨41,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨42,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨43,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨44,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨45,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨46,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨47,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨48,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨49,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨50,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨51,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12501) (by norm_num)
        (q := 1 - (cell12501 ⟨52,by decide⟩).lower)
        (by norm_num [cell12501]) (by norm_num [cell12501])
      exact ⟨E.1,E.2.trans (by norm_num [cell12501])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12501

/-! Source-cell containment and simple scalar guards at 12501. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12501)
open BstLean.Part268 (cell12501)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12501 ⟨10,by decide⟩).lower ∧ (cell12501 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12501 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12501 ⟨11,by decide⟩).lower ∧ (cell12501 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12501 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12501 ⟨12,by decide⟩).lower ∧ (cell12501 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12501 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12501 ⟨13,by decide⟩).lower ∧ (cell12501 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12501 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12501 ⟨14,by decide⟩).lower ∧ (cell12501 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12501 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12501 ⟨15,by decide⟩).lower ∧ (cell12501 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12501 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12501 ⟨16,by decide⟩).lower ∧ (cell12501 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12501 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12501 ⟨17,by decide⟩).lower ∧ (cell12501 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12501 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12501 ⟨18,by decide⟩).lower ∧ (cell12501 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12501 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12501 ⟨19,by decide⟩).lower ∧ (cell12501 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12501 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12501 ⟨20,by decide⟩).lower ∧ (cell12501 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12501 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12501 ⟨21,by decide⟩).lower ∧ (cell12501 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12501 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12501 ⟨22,by decide⟩).lower ∧ (cell12501 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12501 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12501 ⟨23,by decide⟩).lower ∧ (cell12501 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12501 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12501 ⟨24,by decide⟩).lower ∧ (cell12501 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12501 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12501 ⟨25,by decide⟩).lower ∧ (cell12501 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12501 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12501 ⟨26,by decide⟩).lower ∧ (cell12501 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12501 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12501 ⟨27,by decide⟩).lower ∧ (cell12501 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12501 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12501 ⟨28,by decide⟩).lower ∧ (cell12501 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12501 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12501 ⟨29,by decide⟩).lower ∧ (cell12501 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12501 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12501 ⟨30,by decide⟩).lower ∧ (cell12501 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12501 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12501 ⟨31,by decide⟩).lower ∧ (cell12501 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12501 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12501 ⟨32,by decide⟩).lower ∧ (cell12501 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12501 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12501 ⟨33,by decide⟩).lower ∧ (cell12501 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12501 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12501 ⟨34,by decide⟩).lower ∧ (cell12501 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12501 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12501 ⟨35,by decide⟩).lower ∧ (cell12501 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12501 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12501 ⟨36,by decide⟩).lower ∧ (cell12501 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12501 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12501 ⟨37,by decide⟩).lower ∧ (cell12501 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12501 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12501 ⟨38,by decide⟩).lower ∧ (cell12501 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12501 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12501 ⟨39,by decide⟩).lower ∧ (cell12501 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12501 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12501 ⟨40,by decide⟩).lower ∧ (cell12501 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12501 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12501 ⟨41,by decide⟩).lower ∧ (cell12501 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12501 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12501 ⟨42,by decide⟩).lower ∧ (cell12501 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12501 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12501 ⟨43,by decide⟩).lower ∧ (cell12501 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12501 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12501 ⟨44,by decide⟩).lower ∧ (cell12501 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12501 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12501 ⟨45,by decide⟩).lower ∧ (cell12501 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12501 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12501 ⟨46,by decide⟩).lower ∧ (cell12501 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12501 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12501 ⟨47,by decide⟩).lower ∧ (cell12501 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12501 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12501 ⟨48,by decide⟩).lower ∧ (cell12501 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12501 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12501 ⟨49,by decide⟩).lower ∧ (cell12501 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12501 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12501 ⟨50,by decide⟩).lower ∧ (cell12501 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12501 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12501 ⟨51,by decide⟩).lower ∧ (cell12501 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12501 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12501 ⟨52,by decide⟩).lower ∧ (cell12501 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12501 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12501 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12501 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12501,cell12501,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12501 i).lower ∧
    (cell12501 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12501 i).upper ≤ (0.532 : ℝ) ∧
    (cell12501 i).centre ≤ (0.1 : ℝ) ∧ (cell12501 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12501 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12501 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12501

/-! The local source numeric instances at 12501 have no network premises. -/
namespace BstLean.Part269.N12501
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12501)
open BstLean.Part268 (cell12501)

noncomputable def sourceNumerics12501 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12501 (cell12501 i)
      scalarRow12501.M scalarRow12501.H scalarRow12501.xi := by
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
    energy_allowance := scalarRow12501.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12501]
    centre_nonneg := (scalarRow12501.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12501])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12501
/-! Actual 12502 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12502 ≤ (1.036094174625 : ℝ) := by
  have hr : (111.812342789157 : ℝ) ≤ √(12502 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.812342789157 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12502 12502 (11 / 1000) ≤
    (0.008549030129 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12502) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.812342789157 : ℝ) ≤ √(12502 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12502)
  have hdiv : K / √(12502 : ℝ) ≤ K / 111.812342789157 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.812342789157 ≤ (0.008549030129 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12502.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12502 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12502 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12502 := gPlus_lower 12502
end BstLean.Part269.N12502

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12502
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036094174624 : ℝ) ≤ wn 12502 := by
  have hn : √(12502 : ℝ) ≤ 111.812342789158 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12502 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.812342789158 ≤ 2 / √(12502 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255940414 : ℝ) ≤ rhoBar 12502 BstLean.Part154.csC ∧
    rhoBar 12502 BstLean.Part154.csC ≤ 0.000255940810 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036094174624 : ℝ) / (1.295212 * 12502) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036094174625 : ℝ) / (1.29521 * 12502) := by gcongr
      _ ≤ (0.000255940810 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12502 BstLean.Part154.csC) ≤ 0.001023828746 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12502 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) ≤ 0.000195489464 ∧
    cc1 (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) ≤ 0.000124391214 ∧
    cc2 (rhoBar 12502 BstLean.Part154.csC) ≤ 0.000072210016 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12502 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12502 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12502 BstLean.Part154.csC * nuR (rhoBar 12502 BstLean.Part154.csC)) ≤ 0.000511897997 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255940810 : ℝ) * 0.001023828746 := by gcongr
      _ ≤ (0.000511897997 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12502 BstLean.Part154.csC) * nuR (rhoBar 12502 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023828746 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12502 BstLean.Part154.csC) * rhoBar 12502 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255940810 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255940810 / 2 + 0.399 * 0.001023828746 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195489464 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511897997 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124391214 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255940810 / 1.414213562 := by gcongr
      _ ≤ (0.000072210016 : ℝ) := by norm_num

end BstLean.Part269.N12502

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12502
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) ≤ 1.65037E-7 := by
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12502 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12502 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12502 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195489464 : ℝ) ^ 2 + 0.000124391214 ^ 2 + 3 * 0.000072210016 ^ 2 +
        2 * 0.797885 * 0.000195489464 * 0.000124391214 + 2 * 0.000195489464 * 0.000072210016 +
        4 * 0.797885 * 0.000124391214 * 0.000072210016 := by gcongr
    _ ≤ (1.65037E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12502 BstLean.Part154.csC Θ ≤ 0.002672401309 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12502 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12502 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12502 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036094174625 * 1.65037E-7 / (0.000255940414 : ℝ) := by gcongr
    _ ≤ 0.002672401309 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12502 BstLean.Part154.csC Θ ≤ 0.002965990759 + 0.000675272365 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12502 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12502 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036094174625 : ℝ) * ((2 * Θ * 0.000255940810 +
        (6863 / 10000) * 0.000255940810 * 12502 * 0.001023828746) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002965990759 + 0.000675272365 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12502 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12502 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12502 0.011 Θ ∧ gammaRatio 12502 0.011 Θ ≤ 0.000087985832 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12502 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036094174625 : ℝ) * 0.525 / ((1 - 0.011) * 12502) := by gcongr
      _ ≤ (0.000087985832 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12502 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12502 0.011 Θ) :=
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
    badAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12502 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12502 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12502 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12502 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12502 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12502 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12502 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12502 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12502 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12502 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036094174625 : ℝ) * 12502 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003740409587 + 0.003347673674 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12502

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12502
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12502 BstLean.Part154.csC) (piBar (rhoBar 12502 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12502 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12502 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12502 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12502 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12502 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12502 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12502 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12502 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12502 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12502 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052902813757 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12502) ≤ 0.010680731226 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12502 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036094174625)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010680731226 + 2 * 0.737676 / 12502) := by gcongr
    _ ≤ (0.052902813757 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12502 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12502

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12502
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494472332 : ℝ) ≤ plow 12502 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12502) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004538266)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403010688) : eMP 12502 0.011 xi bn ≤ 0.001207586355 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12502 : ℝ) * (1 - 0.011))) ≤ 0.000597059424 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001403010688 / (12502 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597059424 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597059424 : ℝ) + 3.141593 * 0.053004538266 / (12502 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207586355 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004538266)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403010688) : PiBarMP 12502 12 0.011 xi bn ≤ 0.162535974481 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12502 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037456784273 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.195674376299 : ℝ) ≤ √((12502 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.812342789157 : ℝ) ≤ √(12502 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12502) ≤ 0.124605279840 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037456784273 + 0.053004538266 * 1.772454 / (2 * (111.195674376299 : ℝ))) * (1 + 0.001207586355) +
        8 / (12502 * 111.812342789157) + 0.124605279840 := by gcongr
    _ ≤ (0.162535974481 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004538266)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403010688) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283129958695) :
    parallelOracle 12502 0.011 xi bn cd ≤ 0.163542684027 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12502 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12502 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494472332 : ℝ) ≤ plow 12502 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.812342789157 : ℝ) ≤ √(12502 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283129958695 : ℝ) / (2 * 0.560494472332 * 111.812342789157)) * 0.162535974481 +
        0.283129958695 ^ 2 / (2 * 0.560494472332 * 111.812342789157) := by gcongr
    _ ≤ (0.163542684027 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004538266) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001403010688)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283129958695) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12502 12502 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494472332 : ℝ) ≤ plow 12502 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.812342789157 : ℝ) ≤ √(12502 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12502 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12502 Θ 1.22 ≤ 0.011860054686 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.812342789157 := by gcongr <;> linarith
      _ ≤ (0.011860054686 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12502 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12502 12502 0.011 ≤ 0.008549030129 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12502 12502 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12502 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12502 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12502 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12502 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163542684027 + 0.011860054686 + (0.008549030129 : ℝ) *
        (1 + 2 * (0.283129958695 + 0.011860054686) / (0.560494472332 * 111.812342789157))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12502]

end BstLean.Part269.N12502

/-! The original eight local profiles supply actual 12502 moment certificates. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12502 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053004538266 ∧
    0 ≤ bN 12502 BstLean.Part154.csC (groupTheta g) ∧ bN 12502 BstLean.Part154.csC (groupTheta g) ≤ 0.001403010688 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12502 12502 0.011
      (momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12502 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12502 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12502 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230227144938 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12502 0.011
      (momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12502 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12502
/-! The actual computed-centre upper energy formula at 12502. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12502

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12502)
open BstLean.Part268 (cell12502)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086090446146
  | 2 => 0.087044756016
  | 3 => 0.087998976553
  | 4 => 0.088954927344
  | 5 => 0.089914794897
  | 6 => 0.090881185234
  | 7 => 0.091857181093
  | 8 => 0.092846403707
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12502 12502 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12502 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12502

/-! Actual upper energy certificates on all 43 source endpoints at 12502. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12502)
open BstLean.Part268 (cell12502)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12502 (gMinus 12502) (1 - (cell12502 i).lower) ≤ 1 ∧
    energyUpper 12502 (gMinus 12502) (BstLean.Part211.gPlus 12502)
      (finiteEnergy 12502 12502 0.011) (1 - (cell12502 i).lower) ≤
      (cell12502 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨10,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨11,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨12,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨13,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨14,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨15,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨16,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨17,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨18,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨19,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨20,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨21,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨22,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨23,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨24,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨25,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨26,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨27,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨28,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨29,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨30,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨31,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨32,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨33,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨34,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨35,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨36,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨37,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨38,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨39,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨40,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨41,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨42,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨43,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨44,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨45,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨46,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨47,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨48,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨49,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨50,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨51,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12502) (by norm_num)
        (q := 1 - (cell12502 ⟨52,by decide⟩).lower)
        (by norm_num [cell12502]) (by norm_num [cell12502])
      exact ⟨E.1,E.2.trans (by norm_num [cell12502])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12502

/-! Source-cell containment and simple scalar guards at 12502. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12502)
open BstLean.Part268 (cell12502)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12502 ⟨10,by decide⟩).lower ∧ (cell12502 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12502 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12502 ⟨11,by decide⟩).lower ∧ (cell12502 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12502 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12502 ⟨12,by decide⟩).lower ∧ (cell12502 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12502 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12502 ⟨13,by decide⟩).lower ∧ (cell12502 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12502 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12502 ⟨14,by decide⟩).lower ∧ (cell12502 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12502 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12502 ⟨15,by decide⟩).lower ∧ (cell12502 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12502 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12502 ⟨16,by decide⟩).lower ∧ (cell12502 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12502 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12502 ⟨17,by decide⟩).lower ∧ (cell12502 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12502 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12502 ⟨18,by decide⟩).lower ∧ (cell12502 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12502 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12502 ⟨19,by decide⟩).lower ∧ (cell12502 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12502 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12502 ⟨20,by decide⟩).lower ∧ (cell12502 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12502 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12502 ⟨21,by decide⟩).lower ∧ (cell12502 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12502 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12502 ⟨22,by decide⟩).lower ∧ (cell12502 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12502 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12502 ⟨23,by decide⟩).lower ∧ (cell12502 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12502 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12502 ⟨24,by decide⟩).lower ∧ (cell12502 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12502 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12502 ⟨25,by decide⟩).lower ∧ (cell12502 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12502 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12502 ⟨26,by decide⟩).lower ∧ (cell12502 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12502 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12502 ⟨27,by decide⟩).lower ∧ (cell12502 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12502 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12502 ⟨28,by decide⟩).lower ∧ (cell12502 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12502 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12502 ⟨29,by decide⟩).lower ∧ (cell12502 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12502 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12502 ⟨30,by decide⟩).lower ∧ (cell12502 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12502 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12502 ⟨31,by decide⟩).lower ∧ (cell12502 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12502 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12502 ⟨32,by decide⟩).lower ∧ (cell12502 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12502 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12502 ⟨33,by decide⟩).lower ∧ (cell12502 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12502 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12502 ⟨34,by decide⟩).lower ∧ (cell12502 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12502 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12502 ⟨35,by decide⟩).lower ∧ (cell12502 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12502 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12502 ⟨36,by decide⟩).lower ∧ (cell12502 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12502 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12502 ⟨37,by decide⟩).lower ∧ (cell12502 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12502 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12502 ⟨38,by decide⟩).lower ∧ (cell12502 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12502 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12502 ⟨39,by decide⟩).lower ∧ (cell12502 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12502 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12502 ⟨40,by decide⟩).lower ∧ (cell12502 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12502 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12502 ⟨41,by decide⟩).lower ∧ (cell12502 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12502 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12502 ⟨42,by decide⟩).lower ∧ (cell12502 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12502 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12502 ⟨43,by decide⟩).lower ∧ (cell12502 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12502 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12502 ⟨44,by decide⟩).lower ∧ (cell12502 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12502 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12502 ⟨45,by decide⟩).lower ∧ (cell12502 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12502 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12502 ⟨46,by decide⟩).lower ∧ (cell12502 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12502 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12502 ⟨47,by decide⟩).lower ∧ (cell12502 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12502 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12502 ⟨48,by decide⟩).lower ∧ (cell12502 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12502 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12502 ⟨49,by decide⟩).lower ∧ (cell12502 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12502 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12502 ⟨50,by decide⟩).lower ∧ (cell12502 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12502 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12502 ⟨51,by decide⟩).lower ∧ (cell12502 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12502 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12502 ⟨52,by decide⟩).lower ∧ (cell12502 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12502 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12502 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12502 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12502,cell12502,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12502 i).lower ∧
    (cell12502 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12502 i).upper ≤ (0.532 : ℝ) ∧
    (cell12502 i).centre ≤ (0.1 : ℝ) ∧ (cell12502 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12502 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12502 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12502

/-! The local source numeric instances at 12502 have no network premises. -/
namespace BstLean.Part269.N12502
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12502)
open BstLean.Part268 (cell12502)

noncomputable def sourceNumerics12502 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12502 (cell12502 i)
      scalarRow12502.M scalarRow12502.H scalarRow12502.xi := by
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
    energy_allowance := scalarRow12502.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12502]
    centre_nonneg := (scalarRow12502.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12502])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12502
/-! Actual 12503 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12503 ≤ (1.036092718381 : ℝ) := by
  have hr : (111.816814477966 : ℝ) ≤ √(12503 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.816814477966 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12503 12503 (11 / 1000) ≤
    (0.008548688241 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12503) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.816814477966 : ℝ) ≤ √(12503 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12503)
  have hdiv : K / √(12503 : ℝ) ≤ K / 111.816814477966 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.816814477966 ≤ (0.008548688241 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12503.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12503 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12503 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12503 := gPlus_lower 12503
end BstLean.Part269.N12503

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12503
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036092718380 : ℝ) ≤ wn 12503 := by
  have hn : √(12503 : ℝ) ≤ 111.816814477967 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12503 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.816814477967 ≤ 2 / √(12503 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255919584 : ℝ) ≤ rhoBar 12503 BstLean.Part154.csC ∧
    rhoBar 12503 BstLean.Part154.csC ≤ 0.000255919980 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036092718380 : ℝ) / (1.295212 * 12503) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036092718381 : ℝ) / (1.29521 * 12503) := by gcongr
      _ ≤ (0.000255919980 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12503 BstLean.Part154.csC) ≤ 0.001023745416 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12503 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) ≤ 0.000195473553 ∧
    cc1 (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) ≤ 0.000124381090 ∧
    cc2 (rhoBar 12503 BstLean.Part154.csC) ≤ 0.000072204139 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12503 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12503 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12503 BstLean.Part154.csC * nuR (rhoBar 12503 BstLean.Part154.csC)) ≤ 0.000511856334 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255919980 : ℝ) * 0.001023745416 := by gcongr
      _ ≤ (0.000511856334 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12503 BstLean.Part154.csC) * nuR (rhoBar 12503 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023745416 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12503 BstLean.Part154.csC) * rhoBar 12503 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255919980 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255919980 / 2 + 0.399 * 0.001023745416 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195473553 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511856334 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124381090 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255919980 / 1.414213562 := by gcongr
      _ ≤ (0.000072204139 : ℝ) := by norm_num

end BstLean.Part269.N12503

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12503
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) ≤ 1.65010E-7 := by
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12503 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12503 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12503 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195473553 : ℝ) ^ 2 + 0.000124381090 ^ 2 + 3 * 0.000072204139 ^ 2 +
        2 * 0.797885 * 0.000195473553 * 0.000124381090 + 2 * 0.000195473553 * 0.000072204139 +
        4 * 0.797885 * 0.000124381090 * 0.000072204139 := by gcongr
    _ ≤ (1.65010E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12503 BstLean.Part154.csC Θ ≤ 0.002672177827 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12503 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12503 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12503 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036092718381 * 1.65010E-7 / (0.000255919584 : ℝ) := by gcongr
    _ ≤ 0.002672177827 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12503 BstLean.Part154.csC Θ ≤ 0.002965741019 + 0.000675216458 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12503 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12503 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036092718381 : ℝ) * ((2 * Θ * 0.000255919980 +
        (6863 / 10000) * 0.000255919980 * 12503 * 0.001023745416) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002965741019 + 0.000675216458 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12503 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12503 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12503 0.011 Θ ∧ gammaRatio 12503 0.011 Θ ≤ 0.000087978672 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12503 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036092718381 : ℝ) * 0.525 / ((1 - 0.011) * 12503) := by gcongr
      _ ≤ (0.000087978672 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12503 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12503 0.011 Θ) :=
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
    badAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12503 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12503 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12503 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12503 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12503 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12503 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12503 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12503 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12503 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12503 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036092718381 : ℝ) * 12503 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003740159847 + 0.003347394285 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12503

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12503
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12503 BstLean.Part154.csC) (piBar (rhoBar 12503 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12503 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12503 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12503 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12503 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12503 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12503 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12503 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12503 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12503 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12503 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052900674993 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12503) ≤ 0.010680304091 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12503 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036092718381)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010680304091 + 2 * 0.737676 / 12503) := by gcongr
    _ ≤ (0.052900674993 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12503 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12503

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12503
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494518995 : ℝ) ≤ plow 12503 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12503) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004141847)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402893360) : eMP 12503 0.011 xi bn ≤ 0.001207487493 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12503 : ℝ) * (1 - 0.011))) ≤ 0.000597010582 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402893360 / (12503 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597010582 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597010582 : ℝ) + 3.141593 * 0.053004141847 / (12503 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207487493 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004141847)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402893360) : PiBarMP 12503 12 0.011 xi bn ≤ 0.162529398755 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12503 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037455218062 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.200121402811 : ℝ) ≤ √((12503 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.816814477966 : ℝ) ≤ √(12503 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12503) ≤ 0.124600296725 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037455218062 + 0.053004141847 * 1.772454 / (2 * (111.200121402811 : ℝ))) * (1 + 0.001207487493) +
        8 / (12503 * 111.816814477966) + 0.124600296725 := by gcongr
    _ ≤ (0.162529398755 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004141847)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402893360) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283126958999) :
    parallelOracle 12503 0.011 xi bn cd ≤ 0.163536035663 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12503 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12503 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494518995 : ℝ) ≤ plow 12503 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.816814477966 : ℝ) ≤ √(12503 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283126958999 : ℝ) / (2 * 0.560494518995 * 111.816814477966)) * 0.162529398755 +
        0.283126958999 ^ 2 / (2 * 0.560494518995 * 111.816814477966) := by gcongr
    _ ≤ (0.163536035663 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053004141847) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402893360)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283126958999) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12503 12503 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494518995 : ℝ) ≤ plow 12503 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.816814477966 : ℝ) ≤ √(12503 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12503 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12503 Θ 1.22 ≤ 0.011859580388 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.816814477966 := by gcongr <;> linarith
      _ ≤ (0.011859580388 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12503 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12503 12503 0.011 ≤ 0.008548688241 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12503 12503 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12503 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12503 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12503 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12503 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163536035663 + 0.011859580388 + (0.008548688241 : ℝ) *
        (1 + 2 * (0.283126958999 + 0.011859580388) / (0.560494518995 * 111.816814477966))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12503]

end BstLean.Part269.N12503

/-! The original eight local profiles supply actual 12503 moment certificates. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12503 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053004141847 ∧
    0 ≤ bN 12503 BstLean.Part154.csC (groupTheta g) ∧ bN 12503 BstLean.Part154.csC (groupTheta g) ≤ 0.001402893360 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12503 12503 0.011
      (momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12503 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12503 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12503 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230226284006 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12503 0.011
      (momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12503 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12503
/-! The actual computed-centre upper energy formula at 12503. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12503

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12503)
open BstLean.Part268 (cell12503)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086087292414
  | 2 => 0.087041538685
  | 3 => 0.087995685458
  | 4 => 0.088951550048
  | 5 => 0.089911316301
  | 6 => 0.090877587147
  | 7 => 0.091853441743
  | 8 => 0.092842497210
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12503 12503 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12503 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12503

/-! Actual upper energy certificates on all 43 source endpoints at 12503. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12503)
open BstLean.Part268 (cell12503)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12503 (gMinus 12503) (1 - (cell12503 i).lower) ≤ 1 ∧
    energyUpper 12503 (gMinus 12503) (BstLean.Part211.gPlus 12503)
      (finiteEnergy 12503 12503 0.011) (1 - (cell12503 i).lower) ≤
      (cell12503 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨10,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨11,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨12,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨13,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨14,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨15,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨16,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨17,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨18,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨19,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨20,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨21,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨22,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨23,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨24,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨25,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨26,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨27,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨28,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨29,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨30,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨31,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨32,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨33,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨34,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨35,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨36,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨37,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨38,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨39,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨40,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨41,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨42,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨43,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨44,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨45,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨46,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨47,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨48,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨49,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨50,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨51,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12503) (by norm_num)
        (q := 1 - (cell12503 ⟨52,by decide⟩).lower)
        (by norm_num [cell12503]) (by norm_num [cell12503])
      exact ⟨E.1,E.2.trans (by norm_num [cell12503])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12503

/-! Source-cell containment and simple scalar guards at 12503. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12503)
open BstLean.Part268 (cell12503)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12503 ⟨10,by decide⟩).lower ∧ (cell12503 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12503 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12503 ⟨11,by decide⟩).lower ∧ (cell12503 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12503 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12503 ⟨12,by decide⟩).lower ∧ (cell12503 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12503 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12503 ⟨13,by decide⟩).lower ∧ (cell12503 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12503 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12503 ⟨14,by decide⟩).lower ∧ (cell12503 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12503 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12503 ⟨15,by decide⟩).lower ∧ (cell12503 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12503 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12503 ⟨16,by decide⟩).lower ∧ (cell12503 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12503 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12503 ⟨17,by decide⟩).lower ∧ (cell12503 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12503 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12503 ⟨18,by decide⟩).lower ∧ (cell12503 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12503 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12503 ⟨19,by decide⟩).lower ∧ (cell12503 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12503 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12503 ⟨20,by decide⟩).lower ∧ (cell12503 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12503 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12503 ⟨21,by decide⟩).lower ∧ (cell12503 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12503 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12503 ⟨22,by decide⟩).lower ∧ (cell12503 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12503 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12503 ⟨23,by decide⟩).lower ∧ (cell12503 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12503 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12503 ⟨24,by decide⟩).lower ∧ (cell12503 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12503 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12503 ⟨25,by decide⟩).lower ∧ (cell12503 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12503 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12503 ⟨26,by decide⟩).lower ∧ (cell12503 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12503 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12503 ⟨27,by decide⟩).lower ∧ (cell12503 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12503 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12503 ⟨28,by decide⟩).lower ∧ (cell12503 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12503 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12503 ⟨29,by decide⟩).lower ∧ (cell12503 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12503 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12503 ⟨30,by decide⟩).lower ∧ (cell12503 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12503 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12503 ⟨31,by decide⟩).lower ∧ (cell12503 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12503 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12503 ⟨32,by decide⟩).lower ∧ (cell12503 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12503 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12503 ⟨33,by decide⟩).lower ∧ (cell12503 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12503 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12503 ⟨34,by decide⟩).lower ∧ (cell12503 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12503 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12503 ⟨35,by decide⟩).lower ∧ (cell12503 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12503 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12503 ⟨36,by decide⟩).lower ∧ (cell12503 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12503 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12503 ⟨37,by decide⟩).lower ∧ (cell12503 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12503 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12503 ⟨38,by decide⟩).lower ∧ (cell12503 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12503 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12503 ⟨39,by decide⟩).lower ∧ (cell12503 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12503 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12503 ⟨40,by decide⟩).lower ∧ (cell12503 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12503 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12503 ⟨41,by decide⟩).lower ∧ (cell12503 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12503 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12503 ⟨42,by decide⟩).lower ∧ (cell12503 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12503 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12503 ⟨43,by decide⟩).lower ∧ (cell12503 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12503 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12503 ⟨44,by decide⟩).lower ∧ (cell12503 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12503 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12503 ⟨45,by decide⟩).lower ∧ (cell12503 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12503 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12503 ⟨46,by decide⟩).lower ∧ (cell12503 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12503 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12503 ⟨47,by decide⟩).lower ∧ (cell12503 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12503 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12503 ⟨48,by decide⟩).lower ∧ (cell12503 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12503 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12503 ⟨49,by decide⟩).lower ∧ (cell12503 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12503 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12503 ⟨50,by decide⟩).lower ∧ (cell12503 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12503 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12503 ⟨51,by decide⟩).lower ∧ (cell12503 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12503 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12503 ⟨52,by decide⟩).lower ∧ (cell12503 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12503 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12503 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12503 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12503,cell12503,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12503 i).lower ∧
    (cell12503 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12503 i).upper ≤ (0.532 : ℝ) ∧
    (cell12503 i).centre ≤ (0.1 : ℝ) ∧ (cell12503 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12503 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12503 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12503

/-! The local source numeric instances at 12503 have no network premises. -/
namespace BstLean.Part269.N12503
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12503)
open BstLean.Part268 (cell12503)

noncomputable def sourceNumerics12503 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12503 (cell12503 i)
      scalarRow12503.M scalarRow12503.H scalarRow12503.xi := by
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
    energy_allowance := scalarRow12503.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12503]
    centre_nonneg := (scalarRow12503.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12503])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12503
/-! Actual 12504 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12504 ≤ (1.036091262313 : ℝ) := by
  have hr : (111.821285987954 : ℝ) ≤ √(12504 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.821285987954 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12504 12504 (11 / 1000) ≤
    (0.008548346393 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12504) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.821285987954 : ℝ) ≤ √(12504 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12504)
  have hdiv : K / √(12504 : ℝ) ≤ K / 111.821285987954 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.821285987954 ≤ (0.008548346393 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12504.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12504 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12504 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12504 := gPlus_lower 12504
end BstLean.Part269.N12504

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12504
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036091262312 : ℝ) ≤ wn 12504 := by
  have hn : √(12504 : ℝ) ≤ 111.821285987955 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12504 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.821285987955 ≤ 2 / √(12504 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255898757 : ℝ) ≤ rhoBar 12504 BstLean.Part154.csC ∧
    rhoBar 12504 BstLean.Part154.csC ≤ 0.000255899154 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036091262312 : ℝ) / (1.295212 * 12504) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036091262313 : ℝ) / (1.29521 * 12504) := by gcongr
      _ ≤ (0.000255899154 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12504 BstLean.Part154.csC) ≤ 0.001023662101 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12504 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) ≤ 0.000195457645 ∧
    cc1 (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) ≤ 0.000124370967 ∧
    cc2 (rhoBar 12504 BstLean.Part154.csC) ≤ 0.000072198263 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12504 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12504 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12504 BstLean.Part154.csC * nuR (rhoBar 12504 BstLean.Part154.csC)) ≤ 0.000511814679 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255899154 : ℝ) * 0.001023662101 := by gcongr
      _ ≤ (0.000511814679 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12504 BstLean.Part154.csC) * nuR (rhoBar 12504 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023662101 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12504 BstLean.Part154.csC) * rhoBar 12504 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255899154 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255899154 / 2 + 0.399 * 0.001023662101 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195457645 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511814679 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124370967 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255899154 / 1.414213562 := by gcongr
      _ ≤ (0.000072198263 : ℝ) := by norm_num

end BstLean.Part269.N12504

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12504
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) ≤ 1.64983E-7 := by
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12504 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12504 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12504 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195457645 : ℝ) ^ 2 + 0.000124370967 ^ 2 + 3 * 0.000072198263 ^ 2 +
        2 * 0.797885 * 0.000195457645 * 0.000124370967 + 2 * 0.000195457645 * 0.000072198263 +
        4 * 0.797885 * 0.000124370967 * 0.000072198263 := by gcongr
    _ ≤ (1.64983E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12504 BstLean.Part154.csC Θ ≤ 0.002671954280 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12504 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12504 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12504 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036091262313 * 1.64983E-7 / (0.000255898757 : ℝ) := by gcongr
    _ ≤ 0.002671954280 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12504 BstLean.Part154.csC Θ ≤ 0.002965491332 + 0.000675160562 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12504 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12504 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036091262313 : ℝ) * ((2 * Θ * 0.000255899154 +
        (6863 / 10000) * 0.000255899154 * 12504 * 0.001023662101) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002965491332 + 0.000675160562 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12504 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12504 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12504 0.011 Θ ∧ gammaRatio 12504 0.011 Θ ≤ 0.000087971512 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12504 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036091262313 : ℝ) * 0.525 / ((1 - 0.011) * 12504) := by gcongr
      _ ≤ (0.000087971512 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12504 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12504 0.011 Θ) :=
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
    badAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12504 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12504 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12504 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12504 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12504 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12504 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12504 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12504 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12504 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12504 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036091262313 : ℝ) * 12504 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003739910160 + 0.003347114842 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12504

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12504
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12504 BstLean.Part154.csC) (piBar (rhoBar 12504 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12504 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12504 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12504 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12504 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12504 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12504 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12504 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12504 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12504 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12504 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052898536485 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12504) ≤ 0.010679877007 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12504 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036091262313)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010679877007 + 2 * 0.737676 / 12504) := by gcongr
    _ ≤ (0.052898536485 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12504 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12504

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12504
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494565650 : ℝ) ≤ plow 12504 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12504) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003745453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402775997) : eMP 12504 0.011 xi bn ≤ 0.001207388625 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12504 : ℝ) * (1 - 0.011))) ≤ 0.000596961737 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402775997 / (12504 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596961737 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596961737 : ℝ) + 3.141593 * 0.053003745453 / (12504 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207388625 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003745453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402775997) : PiBarMP 12504 12 0.011 xi bn ≤ 0.162522823095 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12504 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037453651318 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.204568251488 : ℝ) ≤ √((12504 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.821285987954 : ℝ) ≤ √(12504 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12504) ≤ 0.124595314208 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037453651318 + 0.053003745453 * 1.772454 / (2 * (111.204568251488 : ℝ))) * (1 + 0.001207388625) +
        8 / (12504 * 111.821285987954) + 0.124595314208 := by gcongr
    _ ≤ (0.162522823095 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003745453)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402775997) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283123959610) :
    parallelOracle 12504 0.011 xi bn cd ≤ 0.163529387376 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12504 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12504 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494565650 : ℝ) ≤ plow 12504 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.821285987954 : ℝ) ≤ √(12504 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283123959610 : ℝ) / (2 * 0.560494565650 * 111.821285987954)) * 0.162522823095 +
        0.283123959610 ^ 2 / (2 * 0.560494565650 * 111.821285987954) := by gcongr
    _ ≤ (0.163529387376 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003745453) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402775997)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283123959610) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12504 12504 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494565650 : ℝ) ≤ plow 12504 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.821285987954 : ℝ) ≤ √(12504 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12504 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12504 Θ 1.22 ≤ 0.011859106147 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.821285987954 := by gcongr <;> linarith
      _ ≤ (0.011859106147 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12504 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12504 12504 0.011 ≤ 0.008548346393 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12504 12504 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12504 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12504 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12504 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12504 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163529387376 + 0.011859106147 + (0.008548346393 : ℝ) *
        (1 + 2 * (0.283123959610 + 0.011859106147) / (0.560494565650 * 111.821285987954))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12504]

end BstLean.Part269.N12504

/-! The original eight local profiles supply actual 12504 moment certificates. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12504 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053003745453 ∧
    0 ≤ bN 12504 BstLean.Part154.csC (groupTheta g) ∧ bN 12504 BstLean.Part154.csC (groupTheta g) ≤ 0.001402775997 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12504 12504 0.011
      (momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12504 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12504 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12504 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230225423125 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12504 0.011
      (momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12504 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12504
/-! The actual computed-centre upper energy formula at 12504. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12504

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12504)
open BstLean.Part268 (cell12504)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086084140012
  | 2 => 0.087038322743
  | 3 => 0.087992395823
  | 4 => 0.088948174298
  | 5 => 0.089907839359
  | 6 => 0.090873990841
  | 7 => 0.091849704329
  | 8 => 0.092838592836
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12504 12504 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12504 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12504

/-! Actual upper energy certificates on all 43 source endpoints at 12504. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12504)
open BstLean.Part268 (cell12504)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12504 (gMinus 12504) (1 - (cell12504 i).lower) ≤ 1 ∧
    energyUpper 12504 (gMinus 12504) (BstLean.Part211.gPlus 12504)
      (finiteEnergy 12504 12504 0.011) (1 - (cell12504 i).lower) ≤
      (cell12504 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨10,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨11,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨12,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨13,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨14,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨15,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨16,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨17,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨18,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨19,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨20,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨21,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨22,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨23,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨24,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨25,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨26,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨27,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨28,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨29,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨30,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨31,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨32,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨33,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨34,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨35,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨36,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨37,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨38,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨39,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨40,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨41,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨42,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨43,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨44,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨45,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨46,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨47,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨48,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨49,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨50,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨51,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12504) (by norm_num)
        (q := 1 - (cell12504 ⟨52,by decide⟩).lower)
        (by norm_num [cell12504]) (by norm_num [cell12504])
      exact ⟨E.1,E.2.trans (by norm_num [cell12504])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12504

/-! Source-cell containment and simple scalar guards at 12504. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12504)
open BstLean.Part268 (cell12504)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12504 ⟨10,by decide⟩).lower ∧ (cell12504 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12504 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12504 ⟨11,by decide⟩).lower ∧ (cell12504 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12504 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12504 ⟨12,by decide⟩).lower ∧ (cell12504 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12504 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12504 ⟨13,by decide⟩).lower ∧ (cell12504 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12504 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12504 ⟨14,by decide⟩).lower ∧ (cell12504 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12504 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12504 ⟨15,by decide⟩).lower ∧ (cell12504 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12504 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12504 ⟨16,by decide⟩).lower ∧ (cell12504 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12504 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12504 ⟨17,by decide⟩).lower ∧ (cell12504 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12504 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12504 ⟨18,by decide⟩).lower ∧ (cell12504 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12504 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12504 ⟨19,by decide⟩).lower ∧ (cell12504 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12504 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12504 ⟨20,by decide⟩).lower ∧ (cell12504 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12504 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12504 ⟨21,by decide⟩).lower ∧ (cell12504 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12504 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12504 ⟨22,by decide⟩).lower ∧ (cell12504 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12504 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12504 ⟨23,by decide⟩).lower ∧ (cell12504 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12504 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12504 ⟨24,by decide⟩).lower ∧ (cell12504 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12504 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12504 ⟨25,by decide⟩).lower ∧ (cell12504 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12504 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12504 ⟨26,by decide⟩).lower ∧ (cell12504 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12504 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12504 ⟨27,by decide⟩).lower ∧ (cell12504 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12504 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12504 ⟨28,by decide⟩).lower ∧ (cell12504 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12504 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12504 ⟨29,by decide⟩).lower ∧ (cell12504 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12504 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12504 ⟨30,by decide⟩).lower ∧ (cell12504 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12504 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12504 ⟨31,by decide⟩).lower ∧ (cell12504 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12504 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12504 ⟨32,by decide⟩).lower ∧ (cell12504 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12504 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12504 ⟨33,by decide⟩).lower ∧ (cell12504 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12504 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12504 ⟨34,by decide⟩).lower ∧ (cell12504 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12504 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12504 ⟨35,by decide⟩).lower ∧ (cell12504 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12504 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12504 ⟨36,by decide⟩).lower ∧ (cell12504 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12504 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12504 ⟨37,by decide⟩).lower ∧ (cell12504 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12504 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12504 ⟨38,by decide⟩).lower ∧ (cell12504 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12504 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12504 ⟨39,by decide⟩).lower ∧ (cell12504 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12504 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12504 ⟨40,by decide⟩).lower ∧ (cell12504 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12504 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12504 ⟨41,by decide⟩).lower ∧ (cell12504 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12504 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12504 ⟨42,by decide⟩).lower ∧ (cell12504 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12504 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12504 ⟨43,by decide⟩).lower ∧ (cell12504 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12504 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12504 ⟨44,by decide⟩).lower ∧ (cell12504 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12504 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12504 ⟨45,by decide⟩).lower ∧ (cell12504 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12504 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12504 ⟨46,by decide⟩).lower ∧ (cell12504 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12504 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12504 ⟨47,by decide⟩).lower ∧ (cell12504 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12504 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12504 ⟨48,by decide⟩).lower ∧ (cell12504 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12504 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12504 ⟨49,by decide⟩).lower ∧ (cell12504 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12504 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12504 ⟨50,by decide⟩).lower ∧ (cell12504 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12504 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12504 ⟨51,by decide⟩).lower ∧ (cell12504 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12504 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12504 ⟨52,by decide⟩).lower ∧ (cell12504 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12504 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12504 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12504 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12504,cell12504,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12504 i).lower ∧
    (cell12504 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12504 i).upper ≤ (0.532 : ℝ) ∧
    (cell12504 i).centre ≤ (0.1 : ℝ) ∧ (cell12504 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12504 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12504 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12504

/-! The local source numeric instances at 12504 have no network premises. -/
namespace BstLean.Part269.N12504
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12504)
open BstLean.Part268 (cell12504)

noncomputable def sourceNumerics12504 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12504 (cell12504 i)
      scalarRow12504.M scalarRow12504.H scalarRow12504.xi := by
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
    energy_allowance := scalarRow12504.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12504]
    centre_nonneg := (scalarRow12504.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12504])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12504
/-! Actual 12505 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12505 ≤ (1.036089806420 : ℝ) := by
  have hr : (111.825757319143 : ℝ) ≤ √(12505 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.825757319143 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12505 12505 (11 / 1000) ≤
    (0.008548004586 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12505) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.825757319143 : ℝ) ≤ √(12505 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12505)
  have hdiv : K / √(12505 : ℝ) ≤ K / 111.825757319143 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.825757319143 ≤ (0.008548004586 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12505.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12505 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12505 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12505 := gPlus_lower 12505
end BstLean.Part269.N12505

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12505
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036089806419 : ℝ) ≤ wn 12505 := by
  have hn : √(12505 : ℝ) ≤ 111.825757319144 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12505 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.825757319144 ≤ 2 / √(12505 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255877934 : ℝ) ≤ rhoBar 12505 BstLean.Part154.csC ∧
    rhoBar 12505 BstLean.Part154.csC ≤ 0.000255878330 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036089806419 : ℝ) / (1.295212 * 12505) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036089806420 : ℝ) / (1.29521 * 12505) := by gcongr
      _ ≤ (0.000255878330 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12505 BstLean.Part154.csC) ≤ 0.001023578794 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12505 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) ≤ 0.000195441739 ∧
    cc1 (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) ≤ 0.000124360847 ∧
    cc2 (rhoBar 12505 BstLean.Part154.csC) ≤ 0.000072192388 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12505 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12505 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12505 BstLean.Part154.csC * nuR (rhoBar 12505 BstLean.Part154.csC)) ≤ 0.000511773029 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255878330 : ℝ) * 0.001023578794 := by gcongr
      _ ≤ (0.000511773029 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12505 BstLean.Part154.csC) * nuR (rhoBar 12505 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023578794 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12505 BstLean.Part154.csC) * rhoBar 12505 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255878330 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255878330 / 2 + 0.399 * 0.001023578794 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195441739 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511773029 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124360847 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255878330 / 1.414213562 := by gcongr
      _ ≤ (0.000072192388 : ℝ) := by norm_num

end BstLean.Part269.N12505

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12505
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) ≤ 1.64957E-7 := by
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12505 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12505 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12505 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195441739 : ℝ) ^ 2 + 0.000124360847 ^ 2 + 3 * 0.000072192388 ^ 2 +
        2 * 0.797885 * 0.000195441739 * 0.000124360847 + 2 * 0.000195441739 * 0.000072192388 +
        4 * 0.797885 * 0.000124360847 * 0.000072192388 := by gcongr
    _ ≤ (1.64957E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12505 BstLean.Part154.csC Θ ≤ 0.002671746853 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12505 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12505 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12505 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036089806420 * 1.64957E-7 / (0.000255877934 : ℝ) := by gcongr
    _ ≤ 0.002671746853 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12505 BstLean.Part154.csC Θ ≤ 0.002965241655 + 0.000675104672 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12505 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12505 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036089806420 : ℝ) * ((2 * Θ * 0.000255878330 +
        (6863 / 10000) * 0.000255878330 * 12505 * 0.001023578794) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002965241655 + 0.000675104672 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12505 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12505 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12505 0.011 Θ ∧ gammaRatio 12505 0.011 Θ ≤ 0.000087964353 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12505 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036089806420 : ℝ) * 0.525 / ((1 - 0.011) * 12505) := by gcongr
      _ ≤ (0.000087964353 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12505 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12505 0.011 Θ) :=
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
    badAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12505 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12505 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12505 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12505 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12505 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12505 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12505 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12505 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12505 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12505 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036089806420 : ℝ) * 12505 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003739660483 + 0.003346851525 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12505

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12505
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12505 BstLean.Part154.csC) (piBar (rhoBar 12505 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12505 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12505 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12505 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12505 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12505 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12505 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12505 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12505 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12505 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12505 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052896398235 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12505) ≤ 0.010679449974 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12505 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036089806420)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010679449974 + 2 * 0.737676 / 12505) := by gcongr
    _ ≤ (0.052896398235 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12505 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12505

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12505
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494612299 : ℝ) ≤ plow 12505 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12505) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003357534)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402667098) : eMP 12505 0.011 xi bn ≤ 0.001207293370 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12505 : ℝ) * (1 - 0.011))) ≤ 0.000596914697 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402667098 / (12505 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596914697 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596914697 : ℝ) + 3.141593 * 0.053003357534 / (12505 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207293370 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003357534)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402667098) : PiBarMP 12505 12 0.011 xi bn ≤ 0.162516361310 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12505 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037452197506 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.209014922352 : ℝ) ≤ √((12505 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.825757319143 : ℝ) ≤ √(12505 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12505) ≤ 0.124590332289 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037452197506 + 0.053003357534 * 1.772454 / (2 * (111.209014922352 : ℝ))) * (1 + 0.001207293370) +
        8 / (12505 * 111.825757319143) + 0.124590332289 := by gcongr
    _ ≤ (0.162516361310 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003357534)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402667098) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283120978882) :
    parallelOracle 12505 0.011 xi bn cd ≤ 0.163522853337 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12505 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12505 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494612299 : ℝ) ≤ plow 12505 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.825757319143 : ℝ) ≤ √(12505 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283120978882 : ℝ) / (2 * 0.560494612299 * 111.825757319143)) * 0.162516361310 +
        0.283120978882 ^ 2 / (2 * 0.560494612299 * 111.825757319143) := by gcongr
    _ ≤ (0.163522853337 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053003357534) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402667098)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283120978882) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12505 12505 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494612299 : ℝ) ≤ plow 12505 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.825757319143 : ℝ) ≤ √(12505 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12505 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12505 Θ 1.22 ≤ 0.011858631963 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.825757319143 := by gcongr <;> linarith
      _ ≤ (0.011858631963 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12505 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12505 12505 0.011 ≤ 0.008548004586 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12505 12505 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12505 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12505 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12505 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12505 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163522853337 + 0.011858631963 + (0.008548004586 : ℝ) *
        (1 + 2 * (0.283120978882 + 0.011858631963) / (0.560494612299 * 111.825757319143))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12505]

end BstLean.Part269.N12505

/-! The original eight local profiles supply actual 12505 moment certificates. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12505 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053003357534 ∧
    0 ≤ bN 12505 BstLean.Part154.csC (groupTheta g) ∧ bN 12505 BstLean.Part154.csC (groupTheta g) ≤ 0.001402667098 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12505 12505 0.011
      (momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12505 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12505 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12505 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230224580647 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12505 0.011
      (momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12505 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12505
/-! The actual computed-centre upper energy formula at 12505. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12505

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12505)
open BstLean.Part268 (cell12505)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086080988940
  | 2 => 0.087035108187
  | 3 => 0.087989107644
  | 4 => 0.088944800092
  | 5 => 0.089904364066
  | 6 => 0.090870396314
  | 7 => 0.091845968849
  | 8 => 0.092834690583
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12505 12505 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12505 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12505

/-! Actual upper energy certificates on all 43 source endpoints at 12505. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12505)
open BstLean.Part268 (cell12505)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12505 (gMinus 12505) (1 - (cell12505 i).lower) ≤ 1 ∧
    energyUpper 12505 (gMinus 12505) (BstLean.Part211.gPlus 12505)
      (finiteEnergy 12505 12505 0.011) (1 - (cell12505 i).lower) ≤
      (cell12505 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨10,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨11,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨12,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨13,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨14,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨15,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨16,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨17,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨18,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨19,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨20,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨21,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨22,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨23,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨24,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨25,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨26,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨27,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨28,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨29,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨30,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨31,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨32,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨33,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨34,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨35,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨36,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨37,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨38,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨39,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨40,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨41,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨42,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨43,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨44,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨45,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨46,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨47,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨48,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨49,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨50,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨51,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12505) (by norm_num)
        (q := 1 - (cell12505 ⟨52,by decide⟩).lower)
        (by norm_num [cell12505]) (by norm_num [cell12505])
      exact ⟨E.1,E.2.trans (by norm_num [cell12505])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12505

/-! Source-cell containment and simple scalar guards at 12505. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12505)
open BstLean.Part268 (cell12505)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12505 ⟨10,by decide⟩).lower ∧ (cell12505 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12505 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12505 ⟨11,by decide⟩).lower ∧ (cell12505 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12505 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12505 ⟨12,by decide⟩).lower ∧ (cell12505 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12505 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12505 ⟨13,by decide⟩).lower ∧ (cell12505 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12505 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12505 ⟨14,by decide⟩).lower ∧ (cell12505 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12505 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12505 ⟨15,by decide⟩).lower ∧ (cell12505 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12505 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12505 ⟨16,by decide⟩).lower ∧ (cell12505 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12505 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12505 ⟨17,by decide⟩).lower ∧ (cell12505 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12505 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12505 ⟨18,by decide⟩).lower ∧ (cell12505 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12505 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12505 ⟨19,by decide⟩).lower ∧ (cell12505 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12505 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12505 ⟨20,by decide⟩).lower ∧ (cell12505 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12505 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12505 ⟨21,by decide⟩).lower ∧ (cell12505 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12505 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12505 ⟨22,by decide⟩).lower ∧ (cell12505 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12505 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12505 ⟨23,by decide⟩).lower ∧ (cell12505 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12505 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12505 ⟨24,by decide⟩).lower ∧ (cell12505 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12505 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12505 ⟨25,by decide⟩).lower ∧ (cell12505 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12505 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12505 ⟨26,by decide⟩).lower ∧ (cell12505 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12505 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12505 ⟨27,by decide⟩).lower ∧ (cell12505 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12505 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12505 ⟨28,by decide⟩).lower ∧ (cell12505 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12505 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12505 ⟨29,by decide⟩).lower ∧ (cell12505 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12505 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12505 ⟨30,by decide⟩).lower ∧ (cell12505 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12505 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12505 ⟨31,by decide⟩).lower ∧ (cell12505 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12505 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12505 ⟨32,by decide⟩).lower ∧ (cell12505 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12505 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12505 ⟨33,by decide⟩).lower ∧ (cell12505 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12505 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12505 ⟨34,by decide⟩).lower ∧ (cell12505 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12505 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12505 ⟨35,by decide⟩).lower ∧ (cell12505 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12505 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12505 ⟨36,by decide⟩).lower ∧ (cell12505 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12505 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12505 ⟨37,by decide⟩).lower ∧ (cell12505 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12505 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12505 ⟨38,by decide⟩).lower ∧ (cell12505 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12505 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12505 ⟨39,by decide⟩).lower ∧ (cell12505 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12505 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12505 ⟨40,by decide⟩).lower ∧ (cell12505 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12505 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12505 ⟨41,by decide⟩).lower ∧ (cell12505 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12505 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12505 ⟨42,by decide⟩).lower ∧ (cell12505 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12505 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12505 ⟨43,by decide⟩).lower ∧ (cell12505 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12505 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12505 ⟨44,by decide⟩).lower ∧ (cell12505 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12505 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12505 ⟨45,by decide⟩).lower ∧ (cell12505 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12505 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12505 ⟨46,by decide⟩).lower ∧ (cell12505 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12505 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12505 ⟨47,by decide⟩).lower ∧ (cell12505 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12505 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12505 ⟨48,by decide⟩).lower ∧ (cell12505 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12505 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12505 ⟨49,by decide⟩).lower ∧ (cell12505 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12505 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12505 ⟨50,by decide⟩).lower ∧ (cell12505 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12505 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12505 ⟨51,by decide⟩).lower ∧ (cell12505 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12505 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12505 ⟨52,by decide⟩).lower ∧ (cell12505 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12505 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12505 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12505 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12505,cell12505,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12505 i).lower ∧
    (cell12505 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12505 i).upper ≤ (0.532 : ℝ) ∧
    (cell12505 i).centre ≤ (0.1 : ℝ) ∧ (cell12505 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12505 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12505 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12505

/-! The local source numeric instances at 12505 have no network premises. -/
namespace BstLean.Part269.N12505
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12505)
open BstLean.Part268 (cell12505)

noncomputable def sourceNumerics12505 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12505 (cell12505 i)
      scalarRow12505.M scalarRow12505.H scalarRow12505.xi := by
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
    energy_allowance := scalarRow12505.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12505]
    centre_nonneg := (scalarRow12505.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12505])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12505
/-! Actual 12506 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12506 ≤ (1.036088350703 : ℝ) := by
  have hr : (111.830228471554 : ℝ) ≤ √(12506 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.830228471554 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12506 12506 (11 / 1000) ≤
    (0.008547662821 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12506) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.830228471554 : ℝ) ≤ √(12506 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12506)
  have hdiv : K / √(12506 : ℝ) ≤ K / 111.830228471554 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.830228471554 ≤ (0.008547662821 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12506.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12506 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12506 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12506 := gPlus_lower 12506
end BstLean.Part269.N12506

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12506
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036088350702 : ℝ) ≤ wn 12506 := by
  have hn : √(12506 : ℝ) ≤ 111.830228471555 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12506 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.830228471555 ≤ 2 / √(12506 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255857114 : ℝ) ≤ rhoBar 12506 BstLean.Part154.csC ∧
    rhoBar 12506 BstLean.Part154.csC ≤ 0.000255857510 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036088350702 : ℝ) / (1.295212 * 12506) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036088350703 : ℝ) / (1.29521 * 12506) := by gcongr
      _ ≤ (0.000255857510 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12506 BstLean.Part154.csC) ≤ 0.001023495504 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12506 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) ≤ 0.000195425836 ∧
    cc1 (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) ≤ 0.000124350727 ∧
    cc2 (rhoBar 12506 BstLean.Part154.csC) ≤ 0.000072186514 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12506 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12506 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12506 BstLean.Part154.csC * nuR (rhoBar 12506 BstLean.Part154.csC)) ≤ 0.000511731386 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255857510 : ℝ) * 0.001023495504 := by gcongr
      _ ≤ (0.000511731386 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12506 BstLean.Part154.csC) * nuR (rhoBar 12506 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023495504 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12506 BstLean.Part154.csC) * rhoBar 12506 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255857510 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255857510 / 2 + 0.399 * 0.001023495504 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195425836 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511731386 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124350727 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255857510 / 1.414213562 := by gcongr
      _ ≤ (0.000072186514 : ℝ) := by norm_num

end BstLean.Part269.N12506

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12506
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) ≤ 1.64930E-7 := by
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12506 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12506 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12506 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195425836 : ℝ) ^ 2 + 0.000124350727 ^ 2 + 3 * 0.000072186514 ^ 2 +
        2 * 0.797885 * 0.000195425836 * 0.000124350727 + 2 * 0.000195425836 * 0.000072186514 +
        4 * 0.797885 * 0.000124350727 * 0.000072186514 := by gcongr
    _ ≤ (1.64930E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12506 BstLean.Part154.csC Θ ≤ 0.002671523165 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12506 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12506 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12506 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036088350703 * 1.64930E-7 / (0.000255857114 : ℝ) := by gcongr
    _ ≤ 0.002671523165 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12506 BstLean.Part154.csC Θ ≤ 0.002964992037 + 0.000675048792 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12506 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12506 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036088350703 : ℝ) * ((2 * Θ * 0.000255857510 +
        (6863 / 10000) * 0.000255857510 * 12506 * 0.001023495504) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002964992037 + 0.000675048792 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12506 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12506 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12506 0.011 Θ ∧ gammaRatio 12506 0.011 Θ ≤ 0.000087957196 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12506 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036088350703 : ℝ) * 0.525 / ((1 - 0.011) * 12506) := by gcongr
      _ ≤ (0.000087957196 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12506 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12506 0.011 Θ) :=
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
    badAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12506 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12506 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12506 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12506 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12506 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12506 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12506 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12506 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12506 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12506 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036088350703 : ℝ) * 12506 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003739410865 + 0.003346571957 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12506

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12506
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12506 BstLean.Part154.csC) (piBar (rhoBar 12506 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12506 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12506 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12506 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12506 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12506 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12506 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12506 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12506 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12506 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12506 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052894260247 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12506) ≤ 0.010679022993 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12506 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036088350703)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010679022993 + 2 * 0.737676 / 12506) := by gcongr
    _ ≤ (0.052894260247 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12506 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12506

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12506
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494658939 : ℝ) ≤ plow 12506 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12506) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002961143)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402549662) : eMP 12506 0.011 xi bn ≤ 0.001207194487 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12506 : ℝ) * (1 - 0.011))) ≤ 0.000596865844 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402549662 / (12506 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596865844 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596865844 : ℝ) + 3.141593 * 0.053002961143 / (12506 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207194487 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002961143)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402549662) : PiBarMP 12506 12 0.011 xi bn ≤ 0.162509785748 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12506 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037450629661 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.213461415423 : ℝ) ≤ √((12506 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.830228471554 : ℝ) ≤ √(12506 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12506) ≤ 0.124585350967 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037450629661 + 0.053002961143 * 1.772454 / (2 * (111.213461415423 : ℝ))) * (1 + 0.001207194487) +
        8 / (12506 * 111.830228471554) + 0.124585350967 := by gcongr
    _ ≤ (0.162509785748 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002961143)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402549662) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283117980014) :
    parallelOracle 12506 0.011 xi bn cd ≤ 0.163516205166 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12506 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12506 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494658939 : ℝ) ≤ plow 12506 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.830228471554 : ℝ) ≤ √(12506 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283117980014 : ℝ) / (2 * 0.560494658939 * 111.830228471554)) * 0.162509785748 +
        0.283117980014 ^ 2 / (2 * 0.560494658939 * 111.830228471554) := by gcongr
    _ ≤ (0.163516205166 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002961143) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402549662)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283117980014) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12506 12506 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494658939 : ℝ) ≤ plow 12506 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.830228471554 : ℝ) ≤ √(12506 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12506 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12506 Θ 1.22 ≤ 0.011858157836 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.830228471554 := by gcongr <;> linarith
      _ ≤ (0.011858157836 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12506 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12506 12506 0.011 ≤ 0.008547662821 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12506 12506 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12506 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12506 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12506 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12506 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163516205166 + 0.011858157836 + (0.008547662821 : ℝ) *
        (1 + 2 * (0.283117980014 + 0.011858157836) / (0.560494658939 * 111.830228471554))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12506]

end BstLean.Part269.N12506

/-! The original eight local profiles supply actual 12506 moment certificates. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12506 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053002961143 ∧
    0 ≤ bN 12506 BstLean.Part154.csC (groupTheta g) ∧ bN 12506 BstLean.Part154.csC (groupTheta g) ≤ 0.001402549662 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12506 12506 0.011
      (momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12506 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12506 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12506 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230223719767 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12506 0.011
      (momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12506 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12506
/-! The actual computed-centre upper energy formula at 12506. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12506

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12506)
open BstLean.Part268 (cell12506)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086077839195
  | 2 => 0.087031895015
  | 3 => 0.087985820921
  | 4 => 0.088941427429
  | 5 => 0.089900890422
  | 6 => 0.090866803564
  | 7 => 0.091842235301
  | 8 => 0.092830790448
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12506 12506 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12506 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12506

/-! Actual upper energy certificates on all 43 source endpoints at 12506. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12506)
open BstLean.Part268 (cell12506)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12506 (gMinus 12506) (1 - (cell12506 i).lower) ≤ 1 ∧
    energyUpper 12506 (gMinus 12506) (BstLean.Part211.gPlus 12506)
      (finiteEnergy 12506 12506 0.011) (1 - (cell12506 i).lower) ≤
      (cell12506 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨10,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨11,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨12,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨13,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨14,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨15,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨16,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨17,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨18,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨19,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨20,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨21,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨22,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨23,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨24,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨25,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨26,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨27,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨28,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨29,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨30,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨31,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨32,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨33,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨34,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨35,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨36,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨37,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨38,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨39,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨40,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨41,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨42,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨43,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨44,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨45,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨46,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨47,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨48,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨49,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨50,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨51,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12506) (by norm_num)
        (q := 1 - (cell12506 ⟨52,by decide⟩).lower)
        (by norm_num [cell12506]) (by norm_num [cell12506])
      exact ⟨E.1,E.2.trans (by norm_num [cell12506])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12506

/-! Source-cell containment and simple scalar guards at 12506. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12506)
open BstLean.Part268 (cell12506)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12506 ⟨10,by decide⟩).lower ∧ (cell12506 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12506 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12506 ⟨11,by decide⟩).lower ∧ (cell12506 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12506 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12506 ⟨12,by decide⟩).lower ∧ (cell12506 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12506 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12506 ⟨13,by decide⟩).lower ∧ (cell12506 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12506 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12506 ⟨14,by decide⟩).lower ∧ (cell12506 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12506 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12506 ⟨15,by decide⟩).lower ∧ (cell12506 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12506 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12506 ⟨16,by decide⟩).lower ∧ (cell12506 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12506 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12506 ⟨17,by decide⟩).lower ∧ (cell12506 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12506 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12506 ⟨18,by decide⟩).lower ∧ (cell12506 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12506 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12506 ⟨19,by decide⟩).lower ∧ (cell12506 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12506 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12506 ⟨20,by decide⟩).lower ∧ (cell12506 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12506 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12506 ⟨21,by decide⟩).lower ∧ (cell12506 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12506 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12506 ⟨22,by decide⟩).lower ∧ (cell12506 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12506 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12506 ⟨23,by decide⟩).lower ∧ (cell12506 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12506 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12506 ⟨24,by decide⟩).lower ∧ (cell12506 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12506 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12506 ⟨25,by decide⟩).lower ∧ (cell12506 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12506 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12506 ⟨26,by decide⟩).lower ∧ (cell12506 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12506 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12506 ⟨27,by decide⟩).lower ∧ (cell12506 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12506 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12506 ⟨28,by decide⟩).lower ∧ (cell12506 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12506 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12506 ⟨29,by decide⟩).lower ∧ (cell12506 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12506 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12506 ⟨30,by decide⟩).lower ∧ (cell12506 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12506 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12506 ⟨31,by decide⟩).lower ∧ (cell12506 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12506 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12506 ⟨32,by decide⟩).lower ∧ (cell12506 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12506 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12506 ⟨33,by decide⟩).lower ∧ (cell12506 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12506 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12506 ⟨34,by decide⟩).lower ∧ (cell12506 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12506 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12506 ⟨35,by decide⟩).lower ∧ (cell12506 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12506 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12506 ⟨36,by decide⟩).lower ∧ (cell12506 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12506 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12506 ⟨37,by decide⟩).lower ∧ (cell12506 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12506 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12506 ⟨38,by decide⟩).lower ∧ (cell12506 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12506 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12506 ⟨39,by decide⟩).lower ∧ (cell12506 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12506 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12506 ⟨40,by decide⟩).lower ∧ (cell12506 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12506 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12506 ⟨41,by decide⟩).lower ∧ (cell12506 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12506 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12506 ⟨42,by decide⟩).lower ∧ (cell12506 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12506 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12506 ⟨43,by decide⟩).lower ∧ (cell12506 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12506 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12506 ⟨44,by decide⟩).lower ∧ (cell12506 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12506 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12506 ⟨45,by decide⟩).lower ∧ (cell12506 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12506 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12506 ⟨46,by decide⟩).lower ∧ (cell12506 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12506 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12506 ⟨47,by decide⟩).lower ∧ (cell12506 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12506 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12506 ⟨48,by decide⟩).lower ∧ (cell12506 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12506 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12506 ⟨49,by decide⟩).lower ∧ (cell12506 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12506 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12506 ⟨50,by decide⟩).lower ∧ (cell12506 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12506 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12506 ⟨51,by decide⟩).lower ∧ (cell12506 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12506 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12506 ⟨52,by decide⟩).lower ∧ (cell12506 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12506 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12506 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12506 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12506,cell12506,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12506 i).lower ∧
    (cell12506 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12506 i).upper ≤ (0.532 : ℝ) ∧
    (cell12506 i).centre ≤ (0.1 : ℝ) ∧ (cell12506 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12506 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12506 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12506

/-! The local source numeric instances at 12506 have no network premises. -/
namespace BstLean.Part269.N12506
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12506)
open BstLean.Part268 (cell12506)

noncomputable def sourceNumerics12506 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12506 (cell12506 i)
      scalarRow12506.M scalarRow12506.H scalarRow12506.xi := by
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
    energy_allowance := scalarRow12506.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12506]
    centre_nonneg := (scalarRow12506.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12506])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12506
/-! Actual 12507 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12507 ≤ (1.036086895162 : ℝ) := by
  have hr : (111.834699445207 : ℝ) ≤ √(12507 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.834699445207 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12507 12507 (11 / 1000) ≤
    (0.008547321096 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12507) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.834699445207 : ℝ) ≤ √(12507 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12507)
  have hdiv : K / √(12507 : ℝ) ≤ K / 111.834699445207 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.834699445207 ≤ (0.008547321096 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12507.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12507 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12507 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12507 := gPlus_lower 12507
end BstLean.Part269.N12507

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12507
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036086895161 : ℝ) ≤ wn 12507 := by
  have hn : √(12507 : ℝ) ≤ 111.834699445208 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12507 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.834699445208 ≤ 2 / √(12507 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255836298 : ℝ) ≤ rhoBar 12507 BstLean.Part154.csC ∧
    rhoBar 12507 BstLean.Part154.csC ≤ 0.000255836694 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036086895161 : ℝ) / (1.295212 * 12507) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036086895162 : ℝ) / (1.29521 * 12507) := by gcongr
      _ ≤ (0.000255836694 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12507 BstLean.Part154.csC) ≤ 0.001023412229 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12507 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) ≤ 0.000195409936 ∧
    cc1 (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) ≤ 0.000124340610 ∧
    cc2 (rhoBar 12507 BstLean.Part154.csC) ≤ 0.000072180641 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12507 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12507 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12507 BstLean.Part154.csC * nuR (rhoBar 12507 BstLean.Part154.csC)) ≤ 0.000511689751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255836694 : ℝ) * 0.001023412229 := by gcongr
      _ ≤ (0.000511689751 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12507 BstLean.Part154.csC) * nuR (rhoBar 12507 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023412229 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12507 BstLean.Part154.csC) * rhoBar 12507 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255836694 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255836694 / 2 + 0.399 * 0.001023412229 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195409936 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511689751 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124340610 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255836694 / 1.414213562 := by gcongr
      _ ≤ (0.000072180641 : ℝ) := by norm_num

end BstLean.Part269.N12507

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12507
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) ≤ 1.64903E-7 := by
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12507 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12507 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12507 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195409936 : ℝ) ^ 2 + 0.000124340610 ^ 2 + 3 * 0.000072180641 ^ 2 +
        2 * 0.797885 * 0.000195409936 * 0.000124340610 + 2 * 0.000195409936 * 0.000072180641 +
        4 * 0.797885 * 0.000124340610 * 0.000072180641 := by gcongr
    _ ≤ (1.64903E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12507 BstLean.Part154.csC Θ ≤ 0.002671299400 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12507 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12507 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12507 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036086895162 * 1.64903E-7 / (0.000255836298 : ℝ) := by gcongr
    _ ≤ 0.002671299400 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12507 BstLean.Part154.csC Θ ≤ 0.002964742472 + 0.000674992924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12507 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12507 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036086895162 : ℝ) * ((2 * Θ * 0.000255836694 +
        (6863 / 10000) * 0.000255836694 * 12507 * 0.001023412229) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002964742472 + 0.000674992924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12507 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12507 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12507 0.011 Θ ∧ gammaRatio 12507 0.011 Θ ≤ 0.000087950040 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12507 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036086895162 : ℝ) * 0.525 / ((1 - 0.011) * 12507) := by gcongr
      _ ≤ (0.000087950040 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12507 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12507 0.011 Θ) :=
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
    badAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12507 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12507 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12507 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12507 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12507 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12507 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12507 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12507 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12507 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12507 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036086895162 : ℝ) * 12507 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003739161300 + 0.003346292324 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12507

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12507
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12507 BstLean.Part154.csC) (piBar (rhoBar 12507 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12507 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12507 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12507 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12507 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12507 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12507 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12507 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12507 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12507 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12507 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052892122511 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12507) ≤ 0.010678596062 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12507 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036086895162)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010678596062 + 2 * 0.737676 / 12507) := by gcongr
    _ ≤ (0.052892122511 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12507 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12507

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12507
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494705572 : ℝ) ≤ plow 12507 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12507) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002564771)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402432185) : eMP 12507 0.011 xi bn ≤ 0.001207095594 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12507 : ℝ) * (1 - 0.011))) ≤ 0.000596816986 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402432185 / (12507 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596816986 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596816986 : ℝ) + 3.141593 * 0.053002564771 / (12507 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001207095594 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002564771)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402432185) : PiBarMP 12507 12 0.011 xi bn ≤ 0.162503210174 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12507 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037449061204 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.217907730724 : ℝ) ≤ √((12507 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.834699445207 : ℝ) ≤ √(12507 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12507) ≤ 0.124580370242 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037449061204 + 0.053002564771 * 1.772454 / (2 * (111.217907730724 : ℝ))) * (1 + 0.001207095594) +
        8 / (12507 * 111.834699445207) + 0.124580370242 := by gcongr
    _ ≤ (0.162503210174 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002564771)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402432185) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283114981435) :
    parallelOracle 12507 0.011 xi bn cd ≤ 0.163509556993 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12507 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12507 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494705572 : ℝ) ≤ plow 12507 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.834699445207 : ℝ) ≤ √(12507 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283114981435 : ℝ) / (2 * 0.560494705572 * 111.834699445207)) * 0.162503210174 +
        0.283114981435 ^ 2 / (2 * 0.560494705572 * 111.834699445207) := by gcongr
    _ ≤ (0.163509556993 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002564771) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402432185)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283114981435) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12507 12507 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494705572 : ℝ) ≤ plow 12507 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.834699445207 : ℝ) ≤ √(12507 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12507 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12507 Θ 1.22 ≤ 0.011857683766 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.834699445207 := by gcongr <;> linarith
      _ ≤ (0.011857683766 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12507 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12507 12507 0.011 ≤ 0.008547321096 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12507 12507 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12507 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12507 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12507 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12507 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163509556993 + 0.011857683766 + (0.008547321096 : ℝ) *
        (1 + 2 * (0.283114981435 + 0.011857683766) / (0.560494705572 * 111.834699445207))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12507]

end BstLean.Part269.N12507

/-! The original eight local profiles supply actual 12507 moment certificates. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12507 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053002564771 ∧
    0 ≤ bN 12507 BstLean.Part154.csC (groupTheta g) ∧ bN 12507 BstLean.Part154.csC (groupTheta g) ≤ 0.001402432185 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12507 12507 0.011
      (momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12507 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12507 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12507 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230222858924 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12507 0.011
      (momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12507 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12507
/-! The actual computed-centre upper energy formula at 12507. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12507

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12507)
open BstLean.Part268 (cell12507)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086074690776
  | 2 => 0.087028683228
  | 3 => 0.087982535653
  | 4 => 0.088938056306
  | 5 => 0.089897418424
  | 6 => 0.090863212589
  | 7 => 0.091838503684
  | 8 => 0.092826892429
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12507 12507 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12507 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12507

/-! Actual upper energy certificates on all 43 source endpoints at 12507. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12507)
open BstLean.Part268 (cell12507)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12507 (gMinus 12507) (1 - (cell12507 i).lower) ≤ 1 ∧
    energyUpper 12507 (gMinus 12507) (BstLean.Part211.gPlus 12507)
      (finiteEnergy 12507 12507 0.011) (1 - (cell12507 i).lower) ≤
      (cell12507 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨10,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨11,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨12,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨13,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨14,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨15,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨16,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨17,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨18,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨19,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨20,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨21,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨22,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨23,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨24,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨25,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨26,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨27,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨28,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨29,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨30,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨31,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨32,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨33,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨34,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨35,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨36,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨37,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨38,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨39,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨40,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨41,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨42,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨43,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨44,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨45,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨46,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨47,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨48,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨49,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨50,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨51,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12507) (by norm_num)
        (q := 1 - (cell12507 ⟨52,by decide⟩).lower)
        (by norm_num [cell12507]) (by norm_num [cell12507])
      exact ⟨E.1,E.2.trans (by norm_num [cell12507])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12507

/-! Source-cell containment and simple scalar guards at 12507. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12507)
open BstLean.Part268 (cell12507)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12507 ⟨10,by decide⟩).lower ∧ (cell12507 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12507 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12507 ⟨11,by decide⟩).lower ∧ (cell12507 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12507 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12507 ⟨12,by decide⟩).lower ∧ (cell12507 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12507 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12507 ⟨13,by decide⟩).lower ∧ (cell12507 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12507 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12507 ⟨14,by decide⟩).lower ∧ (cell12507 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12507 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12507 ⟨15,by decide⟩).lower ∧ (cell12507 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12507 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12507 ⟨16,by decide⟩).lower ∧ (cell12507 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12507 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12507 ⟨17,by decide⟩).lower ∧ (cell12507 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12507 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12507 ⟨18,by decide⟩).lower ∧ (cell12507 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12507 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12507 ⟨19,by decide⟩).lower ∧ (cell12507 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12507 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12507 ⟨20,by decide⟩).lower ∧ (cell12507 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12507 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12507 ⟨21,by decide⟩).lower ∧ (cell12507 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12507 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12507 ⟨22,by decide⟩).lower ∧ (cell12507 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12507 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12507 ⟨23,by decide⟩).lower ∧ (cell12507 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12507 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12507 ⟨24,by decide⟩).lower ∧ (cell12507 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12507 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12507 ⟨25,by decide⟩).lower ∧ (cell12507 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12507 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12507 ⟨26,by decide⟩).lower ∧ (cell12507 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12507 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12507 ⟨27,by decide⟩).lower ∧ (cell12507 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12507 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12507 ⟨28,by decide⟩).lower ∧ (cell12507 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12507 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12507 ⟨29,by decide⟩).lower ∧ (cell12507 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12507 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12507 ⟨30,by decide⟩).lower ∧ (cell12507 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12507 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12507 ⟨31,by decide⟩).lower ∧ (cell12507 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12507 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12507 ⟨32,by decide⟩).lower ∧ (cell12507 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12507 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12507 ⟨33,by decide⟩).lower ∧ (cell12507 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12507 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12507 ⟨34,by decide⟩).lower ∧ (cell12507 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12507 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12507 ⟨35,by decide⟩).lower ∧ (cell12507 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12507 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12507 ⟨36,by decide⟩).lower ∧ (cell12507 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12507 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12507 ⟨37,by decide⟩).lower ∧ (cell12507 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12507 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12507 ⟨38,by decide⟩).lower ∧ (cell12507 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12507 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12507 ⟨39,by decide⟩).lower ∧ (cell12507 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12507 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12507 ⟨40,by decide⟩).lower ∧ (cell12507 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12507 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12507 ⟨41,by decide⟩).lower ∧ (cell12507 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12507 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12507 ⟨42,by decide⟩).lower ∧ (cell12507 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12507 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12507 ⟨43,by decide⟩).lower ∧ (cell12507 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12507 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12507 ⟨44,by decide⟩).lower ∧ (cell12507 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12507 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12507 ⟨45,by decide⟩).lower ∧ (cell12507 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12507 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12507 ⟨46,by decide⟩).lower ∧ (cell12507 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12507 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12507 ⟨47,by decide⟩).lower ∧ (cell12507 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12507 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12507 ⟨48,by decide⟩).lower ∧ (cell12507 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12507 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12507 ⟨49,by decide⟩).lower ∧ (cell12507 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12507 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12507 ⟨50,by decide⟩).lower ∧ (cell12507 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12507 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12507 ⟨51,by decide⟩).lower ∧ (cell12507 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12507 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12507 ⟨52,by decide⟩).lower ∧ (cell12507 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12507 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12507 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12507 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12507,cell12507,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12507 i).lower ∧
    (cell12507 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12507 i).upper ≤ (0.532 : ℝ) ∧
    (cell12507 i).centre ≤ (0.1 : ℝ) ∧ (cell12507 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12507 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12507 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12507

/-! The local source numeric instances at 12507 have no network premises. -/
namespace BstLean.Part269.N12507
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12507)
open BstLean.Part268 (cell12507)

noncomputable def sourceNumerics12507 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12507 (cell12507 i)
      scalarRow12507.M scalarRow12507.H scalarRow12507.xi := by
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
    energy_allowance := scalarRow12507.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12507]
    centre_nonneg := (scalarRow12507.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12507])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12507
/-! Actual 12508 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12508 ≤ (1.036085439796 : ℝ) := by
  have hr : (111.839170240126 : ℝ) ≤ √(12508 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.839170240126 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12508 12508 (11 / 1000) ≤
    (0.008546979412 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12508) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.839170240126 : ℝ) ≤ √(12508 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12508)
  have hdiv : K / √(12508 : ℝ) ≤ K / 111.839170240126 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.839170240126 ≤ (0.008546979412 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12508.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12508 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12508 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12508 := gPlus_lower 12508
end BstLean.Part269.N12508

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12508
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036085439795 : ℝ) ≤ wn 12508 := by
  have hn : √(12508 : ℝ) ≤ 111.839170240127 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12508 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.839170240127 ≤ 2 / √(12508 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255815485 : ℝ) ≤ rhoBar 12508 BstLean.Part154.csC ∧
    rhoBar 12508 BstLean.Part154.csC ≤ 0.000255815881 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036085439795 : ℝ) / (1.295212 * 12508) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036085439796 : ℝ) / (1.29521 * 12508) := by gcongr
      _ ≤ (0.000255815881 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12508 BstLean.Part154.csC) ≤ 0.001023328966 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12508 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) ≤ 0.000195394038 ∧
    cc1 (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) ≤ 0.000124330494 ∧
    cc2 (rhoBar 12508 BstLean.Part154.csC) ≤ 0.000072174769 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12508 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12508 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12508 BstLean.Part154.csC * nuR (rhoBar 12508 BstLean.Part154.csC)) ≤ 0.000511648123 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255815881 : ℝ) * 0.001023328966 := by gcongr
      _ ≤ (0.000511648123 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12508 BstLean.Part154.csC) * nuR (rhoBar 12508 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023328966 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12508 BstLean.Part154.csC) * rhoBar 12508 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255815881 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255815881 / 2 + 0.399 * 0.001023328966 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195394038 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511648123 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124330494 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255815881 / 1.414213562 := by gcongr
      _ ≤ (0.000072174769 : ℝ) := by norm_num

end BstLean.Part269.N12508

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12508
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) ≤ 1.64876E-7 := by
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12508 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12508 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12508 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195394038 : ℝ) ^ 2 + 0.000124330494 ^ 2 + 3 * 0.000072174769 ^ 2 +
        2 * 0.797885 * 0.000195394038 * 0.000124330494 + 2 * 0.000195394038 * 0.000072174769 +
        4 * 0.797885 * 0.000124330494 * 0.000072174769 := by gcongr
    _ ≤ (1.64876E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12508 BstLean.Part154.csC Θ ≤ 0.002671075568 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12508 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12508 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12508 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036085439796 * 1.64876E-7 / (0.000255815485 : ℝ) := by gcongr
    _ ≤ 0.002671075568 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12508 BstLean.Part154.csC Θ ≤ 0.002964492939 + 0.000674937063 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12508 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12508 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036085439796 : ℝ) * ((2 * Θ * 0.000255815881 +
        (6863 / 10000) * 0.000255815881 * 12508 * 0.001023328966) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002964492939 + 0.000674937063 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12508 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12508 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12508 0.011 Θ ∧ gammaRatio 12508 0.011 Θ ≤ 0.000087942885 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12508 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036085439796 : ℝ) * 0.525 / ((1 - 0.011) * 12508) := by gcongr
      _ ≤ (0.000087942885 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12508 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12508 0.011 Θ) :=
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
    badAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12508 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12508 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12508 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12508 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12508 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12508 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12508 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12508 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12508 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12508 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036085439796 : ℝ) * 12508 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003738911767 + 0.003346012631 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12508

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12508
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12508 BstLean.Part154.csC) (piBar (rhoBar 12508 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12508 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12508 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12508 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12508 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12508 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12508 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12508 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12508 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12508 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12508 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052889985037 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12508) ≤ 0.010678169183 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12508 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036085439796)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010678169183 + 2 * 0.737676 / 12508) := by gcongr
    _ ≤ (0.052889985037 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12508 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12508

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12508
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494752198 : ℝ) ≤ plow 12508 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12508) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002168399)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402314674) : eMP 12508 0.011 xi bn ≤ 0.001206996693 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12508 : ℝ) * (1 - 0.011))) ≤ 0.000596768124 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402314674 / (12508 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596768124 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596768124 : ℝ) + 3.141593 * 0.053002168399 / (12508 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206996693 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002168399)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402314674) : PiBarMP 12508 12 0.011 xi bn ≤ 0.162496634678 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12508 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037447492226 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.222353868275 : ℝ) ≤ √((12508 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.839170240126 : ℝ) ≤ √(12508 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12508) ≤ 0.124575390115 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037447492226 + 0.053002168399 * 1.772454 / (2 * (111.222353868275 : ℝ))) * (1 + 0.001206996693) +
        8 / (12508 * 111.839170240126) + 0.124575390115 := by gcongr
    _ ≤ (0.162496634678 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002168399)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402314674) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283111983115) :
    parallelOracle 12508 0.011 xi bn cd ≤ 0.163502908908 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12508 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12508 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494752198 : ℝ) ≤ plow 12508 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.839170240126 : ℝ) ≤ √(12508 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283111983115 : ℝ) / (2 * 0.560494752198 * 111.839170240126)) * 0.162496634678 +
        0.283111983115 ^ 2 / (2 * 0.560494752198 * 111.839170240126) := by gcongr
    _ ≤ (0.163502908908 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053002168399) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402314674)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283111983115) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12508 12508 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494752198 : ℝ) ≤ plow 12508 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.839170240126 : ℝ) ≤ √(12508 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12508 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12508 Θ 1.22 ≤ 0.011857209752 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.839170240126 := by gcongr <;> linarith
      _ ≤ (0.011857209752 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12508 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12508 12508 0.011 ≤ 0.008546979412 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12508 12508 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12508 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12508 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12508 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12508 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163502908908 + 0.011857209752 + (0.008546979412 : ℝ) *
        (1 + 2 * (0.283111983115 + 0.011857209752) / (0.560494752198 * 111.839170240126))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12508]

end BstLean.Part269.N12508

/-! The original eight local profiles supply actual 12508 moment certificates. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12508 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053002168399 ∧
    0 ≤ bN 12508 BstLean.Part154.csC (groupTheta g) ∧ bN 12508 BstLean.Part154.csC (groupTheta g) ≤ 0.001402314674 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12508 12508 0.011
      (momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12508 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12508 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12508 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230221998078 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12508 0.011
      (momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12508 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12508
/-! The actual computed-centre upper energy formula at 12508. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12508

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12508)
open BstLean.Part268 (cell12508)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086071543681
  | 2 => 0.087025472821
  | 3 => 0.087979251836
  | 4 => 0.088934686723
  | 5 => 0.089893948072
  | 6 => 0.090859623387
  | 7 => 0.091834773994
  | 8 => 0.092822996524
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12508 12508 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12508 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12508

/-! Actual upper energy certificates on all 43 source endpoints at 12508. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12508)
open BstLean.Part268 (cell12508)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12508 (gMinus 12508) (1 - (cell12508 i).lower) ≤ 1 ∧
    energyUpper 12508 (gMinus 12508) (BstLean.Part211.gPlus 12508)
      (finiteEnergy 12508 12508 0.011) (1 - (cell12508 i).lower) ≤
      (cell12508 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨10,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨11,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨12,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨13,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨14,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨15,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨16,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨17,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨18,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨19,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨20,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨21,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨22,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨23,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨24,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨25,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨26,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨27,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨28,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨29,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨30,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨31,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨32,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨33,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨34,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨35,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨36,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨37,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨38,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨39,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨40,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨41,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨42,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨43,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨44,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨45,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨46,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨47,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨48,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨49,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨50,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨51,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12508) (by norm_num)
        (q := 1 - (cell12508 ⟨52,by decide⟩).lower)
        (by norm_num [cell12508]) (by norm_num [cell12508])
      exact ⟨E.1,E.2.trans (by norm_num [cell12508])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12508

/-! Source-cell containment and simple scalar guards at 12508. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12508)
open BstLean.Part268 (cell12508)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12508 ⟨10,by decide⟩).lower ∧ (cell12508 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12508 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12508 ⟨11,by decide⟩).lower ∧ (cell12508 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12508 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12508 ⟨12,by decide⟩).lower ∧ (cell12508 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12508 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12508 ⟨13,by decide⟩).lower ∧ (cell12508 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12508 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12508 ⟨14,by decide⟩).lower ∧ (cell12508 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12508 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12508 ⟨15,by decide⟩).lower ∧ (cell12508 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12508 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12508 ⟨16,by decide⟩).lower ∧ (cell12508 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12508 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12508 ⟨17,by decide⟩).lower ∧ (cell12508 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12508 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12508 ⟨18,by decide⟩).lower ∧ (cell12508 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12508 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12508 ⟨19,by decide⟩).lower ∧ (cell12508 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12508 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12508 ⟨20,by decide⟩).lower ∧ (cell12508 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12508 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12508 ⟨21,by decide⟩).lower ∧ (cell12508 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12508 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12508 ⟨22,by decide⟩).lower ∧ (cell12508 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12508 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12508 ⟨23,by decide⟩).lower ∧ (cell12508 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12508 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12508 ⟨24,by decide⟩).lower ∧ (cell12508 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12508 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12508 ⟨25,by decide⟩).lower ∧ (cell12508 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12508 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12508 ⟨26,by decide⟩).lower ∧ (cell12508 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12508 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12508 ⟨27,by decide⟩).lower ∧ (cell12508 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12508 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12508 ⟨28,by decide⟩).lower ∧ (cell12508 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12508 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12508 ⟨29,by decide⟩).lower ∧ (cell12508 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12508 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12508 ⟨30,by decide⟩).lower ∧ (cell12508 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12508 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12508 ⟨31,by decide⟩).lower ∧ (cell12508 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12508 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12508 ⟨32,by decide⟩).lower ∧ (cell12508 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12508 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12508 ⟨33,by decide⟩).lower ∧ (cell12508 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12508 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12508 ⟨34,by decide⟩).lower ∧ (cell12508 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12508 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12508 ⟨35,by decide⟩).lower ∧ (cell12508 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12508 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12508 ⟨36,by decide⟩).lower ∧ (cell12508 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12508 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12508 ⟨37,by decide⟩).lower ∧ (cell12508 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12508 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12508 ⟨38,by decide⟩).lower ∧ (cell12508 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12508 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12508 ⟨39,by decide⟩).lower ∧ (cell12508 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12508 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12508 ⟨40,by decide⟩).lower ∧ (cell12508 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12508 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12508 ⟨41,by decide⟩).lower ∧ (cell12508 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12508 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12508 ⟨42,by decide⟩).lower ∧ (cell12508 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12508 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12508 ⟨43,by decide⟩).lower ∧ (cell12508 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12508 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12508 ⟨44,by decide⟩).lower ∧ (cell12508 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12508 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12508 ⟨45,by decide⟩).lower ∧ (cell12508 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12508 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12508 ⟨46,by decide⟩).lower ∧ (cell12508 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12508 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12508 ⟨47,by decide⟩).lower ∧ (cell12508 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12508 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12508 ⟨48,by decide⟩).lower ∧ (cell12508 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12508 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12508 ⟨49,by decide⟩).lower ∧ (cell12508 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12508 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12508 ⟨50,by decide⟩).lower ∧ (cell12508 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12508 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12508 ⟨51,by decide⟩).lower ∧ (cell12508 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12508 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12508 ⟨52,by decide⟩).lower ∧ (cell12508 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12508 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12508 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12508 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12508,cell12508,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12508 i).lower ∧
    (cell12508 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12508 i).upper ≤ (0.532 : ℝ) ∧
    (cell12508 i).centre ≤ (0.1 : ℝ) ∧ (cell12508 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12508 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12508 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12508

/-! The local source numeric instances at 12508 have no network premises. -/
namespace BstLean.Part269.N12508
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12508)
open BstLean.Part268 (cell12508)

noncomputable def sourceNumerics12508 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12508 (cell12508 i)
      scalarRow12508.M scalarRow12508.H scalarRow12508.xi := by
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
    energy_allowance := scalarRow12508.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12508]
    centre_nonneg := (scalarRow12508.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12508])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12508
/-! Actual 12509 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12509 ≤ (1.036083984606 : ℝ) := by
  have hr : (111.843640856331 : ℝ) ≤ √(12509 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.843640856331 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12509 12509 (11 / 1000) ≤
    (0.008546637770 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12509) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.843640856331 : ℝ) ≤ √(12509 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12509)
  have hdiv : K / √(12509 : ℝ) ≤ K / 111.843640856331 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.843640856331 ≤ (0.008546637770 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12509.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12509 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12509 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12509 := gPlus_lower 12509
end BstLean.Part269.N12509

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12509
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036083984605 : ℝ) ≤ wn 12509 := by
  have hn : √(12509 : ℝ) ≤ 111.843640856332 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12509 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.843640856332 ≤ 2 / √(12509 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255794675 : ℝ) ≤ rhoBar 12509 BstLean.Part154.csC ∧
    rhoBar 12509 BstLean.Part154.csC ≤ 0.000255795071 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036083984605 : ℝ) / (1.295212 * 12509) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036083984606 : ℝ) / (1.29521 * 12509) := by gcongr
      _ ≤ (0.000255795071 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12509 BstLean.Part154.csC) ≤ 0.001023245716 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12509 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) ≤ 0.000195378142 ∧
    cc1 (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) ≤ 0.000124320380 ∧
    cc2 (rhoBar 12509 BstLean.Part154.csC) ≤ 0.000072168898 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12509 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12509 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12509 BstLean.Part154.csC * nuR (rhoBar 12509 BstLean.Part154.csC)) ≤ 0.000511606500 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255795071 : ℝ) * 0.001023245716 := by gcongr
      _ ≤ (0.000511606500 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12509 BstLean.Part154.csC) * nuR (rhoBar 12509 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023245716 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12509 BstLean.Part154.csC) * rhoBar 12509 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255795071 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255795071 / 2 + 0.399 * 0.001023245716 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195378142 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511606500 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124320380 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255795071 / 1.414213562 := by gcongr
      _ ≤ (0.000072168898 : ℝ) := by norm_num

end BstLean.Part269.N12509

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12509
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) ≤ 1.64849E-7 := by
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12509 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12509 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12509 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195378142 : ℝ) ^ 2 + 0.000124320380 ^ 2 + 3 * 0.000072168898 ^ 2 +
        2 * 0.797885 * 0.000195378142 * 0.000124320380 + 2 * 0.000195378142 * 0.000072168898 +
        4 * 0.797885 * 0.000124320380 * 0.000072168898 := by gcongr
    _ ≤ (1.64849E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12509 BstLean.Part154.csC Θ ≤ 0.002670851671 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12509 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12509 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12509 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036083984606 * 1.64849E-7 / (0.000255794675 : ℝ) := by gcongr
    _ ≤ 0.002670851671 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12509 BstLean.Part154.csC Θ ≤ 0.002964243443 + 0.000674881211 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12509 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12509 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036083984606 : ℝ) * ((2 * Θ * 0.000255795071 +
        (6863 / 10000) * 0.000255795071 * 12509 * 0.001023245716) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002964243443 + 0.000674881211 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12509 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12509 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12509 0.011 Θ ∧ gammaRatio 12509 0.011 Θ ≤ 0.000087935731 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12509 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036083984606 : ℝ) * 0.525 / ((1 - 0.011) * 12509) := by gcongr
      _ ≤ (0.000087935731 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12509 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12509 0.011 Θ) :=
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
    badAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12509 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12509 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12509 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12509 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12509 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12509 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12509 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12509 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12509 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12509 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036083984606 : ℝ) * 12509 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003738662271 + 0.003345732882 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12509

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12509
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12509 BstLean.Part154.csC) (piBar (rhoBar 12509 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12509 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12509 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12509 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12509 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12509 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12509 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12509 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12509 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12509 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12509 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052887847821 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12509) ≤ 0.010677742355 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12509 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036083984606)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010677742355 + 2 * 0.737676 / 12509) := by gcongr
    _ ≤ (0.052887847821 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12509 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12509

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12509
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494798816 : ℝ) ≤ plow 12509 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12509) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001772035)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402197128) : eMP 12509 0.011 xi bn ≤ 0.001206897788 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12509 : ℝ) * (1 - 0.011))) ≤ 0.000596719260 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402197128 / (12509 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596719260 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596719260 : ℝ) + 3.141593 * 0.053001772035 / (12509 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206897788 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001772035)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402197128) : PiBarMP 12509 12 0.011 xi bn ≤ 0.162490059249 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12509 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037445922716 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.226799828098 : ℝ) ≤ √((12509 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.843640856331 : ℝ) ≤ √(12509 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12509) ≤ 0.124570410585 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037445922716 + 0.053001772035 * 1.772454 / (2 * (111.226799828098 : ℝ))) * (1 + 0.001206897788) +
        8 / (12509 * 111.843640856331) + 0.124570410585 := by gcongr
    _ ≤ (0.162490059249 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001772035)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402197128) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283108985068) :
    parallelOracle 12509 0.011 xi bn cd ≤ 0.163496260899 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12509 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12509 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494798816 : ℝ) ≤ plow 12509 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.843640856331 : ℝ) ≤ √(12509 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283108985068 : ℝ) / (2 * 0.560494798816 * 111.843640856331)) * 0.162490059249 +
        0.283108985068 ^ 2 / (2 * 0.560494798816 * 111.843640856331) := by gcongr
    _ ≤ (0.163496260899 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001772035) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402197128)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283108985068) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12509 12509 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494798816 : ℝ) ≤ plow 12509 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.843640856331 : ℝ) ≤ √(12509 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12509 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12509 Θ 1.22 ≤ 0.011856735796 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.843640856331 := by gcongr <;> linarith
      _ ≤ (0.011856735796 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12509 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12509 12509 0.011 ≤ 0.008546637770 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12509 12509 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12509 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12509 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12509 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12509 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163496260899 + 0.011856735796 + (0.008546637770 : ℝ) *
        (1 + 2 * (0.283108985068 + 0.011856735796) / (0.560494798816 * 111.843640856331))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12509]

end BstLean.Part269.N12509

/-! The original eight local profiles supply actual 12509 moment certificates. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12509 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053001772035 ∧
    0 ≤ bN 12509 BstLean.Part154.csC (groupTheta g) ∧ bN 12509 BstLean.Part154.csC (groupTheta g) ≤ 0.001402197128 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12509 12509 0.011
      (momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12509 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12509 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12509 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230221137247 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12509 0.011
      (momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12509 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12509
/-! The actual computed-centre upper energy formula at 12509. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12509

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12509)
open BstLean.Part268 (cell12509)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086068397910
  | 2 => 0.087022263796
  | 3 => 0.087975969471
  | 4 => 0.088931318677
  | 5 => 0.089890479362
  | 6 => 0.090856035956
  | 7 => 0.091831046230
  | 8 => 0.092819102729
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12509 12509 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12509 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12509

/-! Actual upper energy certificates on all 43 source endpoints at 12509. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12509)
open BstLean.Part268 (cell12509)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12509 (gMinus 12509) (1 - (cell12509 i).lower) ≤ 1 ∧
    energyUpper 12509 (gMinus 12509) (BstLean.Part211.gPlus 12509)
      (finiteEnergy 12509 12509 0.011) (1 - (cell12509 i).lower) ≤
      (cell12509 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨10,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨11,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨12,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨13,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨14,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨15,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨16,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨17,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨18,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨19,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨20,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨21,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨22,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨23,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨24,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨25,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨26,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨27,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨28,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨29,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨30,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨31,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨32,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨33,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨34,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨35,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨36,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨37,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨38,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨39,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨40,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨41,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨42,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨43,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨44,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨45,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨46,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨47,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨48,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨49,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨50,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨51,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12509) (by norm_num)
        (q := 1 - (cell12509 ⟨52,by decide⟩).lower)
        (by norm_num [cell12509]) (by norm_num [cell12509])
      exact ⟨E.1,E.2.trans (by norm_num [cell12509])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12509

/-! Source-cell containment and simple scalar guards at 12509. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12509)
open BstLean.Part268 (cell12509)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12509 ⟨10,by decide⟩).lower ∧ (cell12509 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12509 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12509 ⟨11,by decide⟩).lower ∧ (cell12509 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12509 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12509 ⟨12,by decide⟩).lower ∧ (cell12509 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12509 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12509 ⟨13,by decide⟩).lower ∧ (cell12509 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12509 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12509 ⟨14,by decide⟩).lower ∧ (cell12509 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12509 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12509 ⟨15,by decide⟩).lower ∧ (cell12509 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12509 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12509 ⟨16,by decide⟩).lower ∧ (cell12509 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12509 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12509 ⟨17,by decide⟩).lower ∧ (cell12509 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12509 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12509 ⟨18,by decide⟩).lower ∧ (cell12509 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12509 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12509 ⟨19,by decide⟩).lower ∧ (cell12509 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12509 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12509 ⟨20,by decide⟩).lower ∧ (cell12509 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12509 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12509 ⟨21,by decide⟩).lower ∧ (cell12509 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12509 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12509 ⟨22,by decide⟩).lower ∧ (cell12509 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12509 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12509 ⟨23,by decide⟩).lower ∧ (cell12509 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12509 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12509 ⟨24,by decide⟩).lower ∧ (cell12509 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12509 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12509 ⟨25,by decide⟩).lower ∧ (cell12509 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12509 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12509 ⟨26,by decide⟩).lower ∧ (cell12509 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12509 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12509 ⟨27,by decide⟩).lower ∧ (cell12509 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12509 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12509 ⟨28,by decide⟩).lower ∧ (cell12509 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12509 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12509 ⟨29,by decide⟩).lower ∧ (cell12509 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12509 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12509 ⟨30,by decide⟩).lower ∧ (cell12509 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12509 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12509 ⟨31,by decide⟩).lower ∧ (cell12509 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12509 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12509 ⟨32,by decide⟩).lower ∧ (cell12509 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12509 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12509 ⟨33,by decide⟩).lower ∧ (cell12509 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12509 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12509 ⟨34,by decide⟩).lower ∧ (cell12509 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12509 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12509 ⟨35,by decide⟩).lower ∧ (cell12509 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12509 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12509 ⟨36,by decide⟩).lower ∧ (cell12509 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12509 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12509 ⟨37,by decide⟩).lower ∧ (cell12509 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12509 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12509 ⟨38,by decide⟩).lower ∧ (cell12509 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12509 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12509 ⟨39,by decide⟩).lower ∧ (cell12509 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12509 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12509 ⟨40,by decide⟩).lower ∧ (cell12509 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12509 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12509 ⟨41,by decide⟩).lower ∧ (cell12509 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12509 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12509 ⟨42,by decide⟩).lower ∧ (cell12509 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12509 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12509 ⟨43,by decide⟩).lower ∧ (cell12509 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12509 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12509 ⟨44,by decide⟩).lower ∧ (cell12509 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12509 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12509 ⟨45,by decide⟩).lower ∧ (cell12509 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12509 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12509 ⟨46,by decide⟩).lower ∧ (cell12509 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12509 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12509 ⟨47,by decide⟩).lower ∧ (cell12509 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12509 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12509 ⟨48,by decide⟩).lower ∧ (cell12509 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12509 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12509 ⟨49,by decide⟩).lower ∧ (cell12509 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12509 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12509 ⟨50,by decide⟩).lower ∧ (cell12509 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12509 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12509 ⟨51,by decide⟩).lower ∧ (cell12509 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12509 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12509 ⟨52,by decide⟩).lower ∧ (cell12509 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12509 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12509 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12509 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12509,cell12509,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12509 i).lower ∧
    (cell12509 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12509 i).upper ≤ (0.532 : ℝ) ∧
    (cell12509 i).centre ≤ (0.1 : ℝ) ∧ (cell12509 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12509 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12509 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12509

/-! The local source numeric instances at 12509 have no network premises. -/
namespace BstLean.Part269.N12509
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12509)
open BstLean.Part268 (cell12509)

noncomputable def sourceNumerics12509 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12509 (cell12509 i)
      scalarRow12509.M scalarRow12509.H scalarRow12509.xi := by
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
    energy_allowance := scalarRow12509.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12509]
    centre_nonneg := (scalarRow12509.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12509])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12509
/-! Actual 12510 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12510 ≤ (1.036082529591 : ℝ) := by
  have hr : (111.848111293843 : ℝ) ≤ √(12510 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.848111293843 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12510 12510 (11 / 1000) ≤
    (0.008546296168 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12510) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.848111293843 : ℝ) ≤ √(12510 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12510)
  have hdiv : K / √(12510 : ℝ) ≤ K / 111.848111293843 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.848111293843 ≤ (0.008546296168 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12510.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12510 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12510 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12510 := gPlus_lower 12510
end BstLean.Part269.N12510

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12510
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036082529590 : ℝ) ≤ wn 12510 := by
  have hn : √(12510 : ℝ) ≤ 111.848111293844 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12510 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.848111293844 ≤ 2 / √(12510 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255773868 : ℝ) ≤ rhoBar 12510 BstLean.Part154.csC ∧
    rhoBar 12510 BstLean.Part154.csC ≤ 0.000255774264 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036082529590 : ℝ) / (1.295212 * 12510) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036082529591 : ℝ) / (1.29521 * 12510) := by gcongr
      _ ≤ (0.000255774264 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12510 BstLean.Part154.csC) ≤ 0.001023162477 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12510 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) ≤ 0.000195362249 ∧
    cc1 (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) ≤ 0.000124310267 ∧
    cc2 (rhoBar 12510 BstLean.Part154.csC) ≤ 0.000072163027 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12510 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12510 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12510 BstLean.Part154.csC * nuR (rhoBar 12510 BstLean.Part154.csC)) ≤ 0.000511564883 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255774264 : ℝ) * 0.001023162477 := by gcongr
      _ ≤ (0.000511564883 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12510 BstLean.Part154.csC) * nuR (rhoBar 12510 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023162477 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12510 BstLean.Part154.csC) * rhoBar 12510 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255774264 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255774264 / 2 + 0.399 * 0.001023162477 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195362249 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511564883 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124310267 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255774264 / 1.414213562 := by gcongr
      _ ≤ (0.000072163027 : ℝ) := by norm_num

end BstLean.Part269.N12510

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12510
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) ≤ 1.64822E-7 := by
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12510 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12510 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12510 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195362249 : ℝ) ^ 2 + 0.000124310267 ^ 2 + 3 * 0.000072163027 ^ 2 +
        2 * 0.797885 * 0.000195362249 * 0.000124310267 + 2 * 0.000195362249 * 0.000072163027 +
        4 * 0.797885 * 0.000124310267 * 0.000072163027 := by gcongr
    _ ≤ (1.64822E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12510 BstLean.Part154.csC Θ ≤ 0.002670627708 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12510 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12510 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12510 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036082529591 * 1.64822E-7 / (0.000255773868 : ℝ) := by gcongr
    _ ≤ 0.002670627708 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12510 BstLean.Part154.csC Θ ≤ 0.002963993976 + 0.000674825367 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12510 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12510 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036082529591 : ℝ) * ((2 * Θ * 0.000255774264 +
        (6863 / 10000) * 0.000255774264 * 12510 * 0.001023162477) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002963993976 + 0.000674825367 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12510 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12510 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12510 0.011 Θ ∧ gammaRatio 12510 0.011 Θ ≤ 0.000087928578 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12510 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036082529591 : ℝ) * 0.525 / ((1 - 0.011) * 12510) := by gcongr
      _ ≤ (0.000087928578 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12510 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12510 0.011 Θ) :=
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
    badAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12510 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12510 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12510 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12510 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12510 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12510 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12510 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12510 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12510 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12510 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036082529591 : ℝ) * 12510 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003738412804 + 0.003345453075 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12510

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12510
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12510 BstLean.Part154.csC) (piBar (rhoBar 12510 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12510 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12510 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12510 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12510 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12510 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12510 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12510 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12510 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12510 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12510 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052885710862 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12510) ≤ 0.010677315578 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12510 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036082529591)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010677315578 + 2 * 0.737676 / 12510) := by gcongr
    _ ≤ (0.052885710862 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12510 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12510

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12510
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494845427 : ℝ) ≤ plow 12510 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12510) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001375669)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402079547) : eMP 12510 0.011 xi bn ≤ 0.001206798874 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12510 : ℝ) * (1 - 0.011))) ≤ 0.000596670391 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001402079547 / (12510 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596670391 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596670391 : ℝ) + 3.141593 * 0.053001375669 / (12510 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206798874 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001375669)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402079547) : PiBarMP 12510 12 0.011 xi bn ≤ 0.162483483884 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12510 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037444352672 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.231245610215 : ℝ) ≤ √((12510 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.848111293843 : ℝ) ≤ √(12510 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12510) ≤ 0.124565431652 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037444352672 + 0.053001375669 * 1.772454 / (2 * (111.231245610215 : ℝ))) * (1 + 0.001206798874) +
        8 / (12510 * 111.848111293843) + 0.124565431652 := by gcongr
    _ ≤ (0.162483483884 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001375669)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402079547) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283105987270) :
    parallelOracle 12510 0.011 xi bn cd ≤ 0.163489612963 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12510 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12510 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494845427 : ℝ) ≤ plow 12510 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.848111293843 : ℝ) ≤ √(12510 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283105987270 : ℝ) / (2 * 0.560494845427 * 111.848111293843)) * 0.162483483884 +
        0.283105987270 ^ 2 / (2 * 0.560494845427 * 111.848111293843) := by gcongr
    _ ≤ (0.163489612963 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053001375669) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001402079547)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283105987270) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12510 12510 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494845427 : ℝ) ≤ plow 12510 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.848111293843 : ℝ) ≤ √(12510 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12510 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12510 Θ 1.22 ≤ 0.011856261896 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.848111293843 := by gcongr <;> linarith
      _ ≤ (0.011856261896 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12510 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12510 12510 0.011 ≤ 0.008546296168 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12510 12510 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12510 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12510 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12510 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12510 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163489612963 + 0.011856261896 + (0.008546296168 : ℝ) *
        (1 + 2 * (0.283105987270 + 0.011856261896) / (0.560494845427 * 111.848111293843))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12510]

end BstLean.Part269.N12510

/-! The original eight local profiles supply actual 12510 moment certificates. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12510 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053001375669 ∧
    0 ≤ bN 12510 BstLean.Part154.csC (groupTheta g) ∧ bN 12510 BstLean.Part154.csC (groupTheta g) ≤ 0.001402079547 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12510 12510 0.011
      (momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12510 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12510 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12510 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230220276408 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12510 0.011
      (momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12510 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12510
/-! The actual computed-centre upper energy formula at 12510. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12510

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12510)
open BstLean.Part268 (cell12510)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086065253461
  | 2 => 0.087019056149
  | 3 => 0.087972688555
  | 4 => 0.088927952167
  | 5 => 0.089887012294
  | 6 => 0.090852450295
  | 7 => 0.091827320389
  | 8 => 0.092815211043
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12510 12510 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12510 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12510

/-! Actual upper energy certificates on all 43 source endpoints at 12510. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12510)
open BstLean.Part268 (cell12510)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12510 (gMinus 12510) (1 - (cell12510 i).lower) ≤ 1 ∧
    energyUpper 12510 (gMinus 12510) (BstLean.Part211.gPlus 12510)
      (finiteEnergy 12510 12510 0.011) (1 - (cell12510 i).lower) ≤
      (cell12510 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨10,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨11,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨12,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨13,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨14,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨15,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨16,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨17,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨18,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨19,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨20,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨21,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨22,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨23,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨24,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨25,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨26,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨27,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨28,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨29,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨30,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨31,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨32,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨33,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨34,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨35,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨36,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨37,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨38,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨39,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨40,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨41,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨42,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨43,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨44,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨45,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨46,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨47,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨48,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨49,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨50,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨51,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12510) (by norm_num)
        (q := 1 - (cell12510 ⟨52,by decide⟩).lower)
        (by norm_num [cell12510]) (by norm_num [cell12510])
      exact ⟨E.1,E.2.trans (by norm_num [cell12510])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12510

/-! Source-cell containment and simple scalar guards at 12510. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12510)
open BstLean.Part268 (cell12510)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12510 ⟨10,by decide⟩).lower ∧ (cell12510 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12510 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12510 ⟨11,by decide⟩).lower ∧ (cell12510 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12510 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12510 ⟨12,by decide⟩).lower ∧ (cell12510 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12510 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12510 ⟨13,by decide⟩).lower ∧ (cell12510 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12510 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12510 ⟨14,by decide⟩).lower ∧ (cell12510 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12510 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12510 ⟨15,by decide⟩).lower ∧ (cell12510 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12510 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12510 ⟨16,by decide⟩).lower ∧ (cell12510 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12510 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12510 ⟨17,by decide⟩).lower ∧ (cell12510 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12510 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12510 ⟨18,by decide⟩).lower ∧ (cell12510 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12510 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12510 ⟨19,by decide⟩).lower ∧ (cell12510 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12510 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12510 ⟨20,by decide⟩).lower ∧ (cell12510 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12510 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12510 ⟨21,by decide⟩).lower ∧ (cell12510 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12510 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12510 ⟨22,by decide⟩).lower ∧ (cell12510 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12510 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12510 ⟨23,by decide⟩).lower ∧ (cell12510 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12510 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12510 ⟨24,by decide⟩).lower ∧ (cell12510 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12510 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12510 ⟨25,by decide⟩).lower ∧ (cell12510 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12510 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12510 ⟨26,by decide⟩).lower ∧ (cell12510 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12510 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12510 ⟨27,by decide⟩).lower ∧ (cell12510 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12510 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12510 ⟨28,by decide⟩).lower ∧ (cell12510 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12510 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12510 ⟨29,by decide⟩).lower ∧ (cell12510 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12510 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12510 ⟨30,by decide⟩).lower ∧ (cell12510 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12510 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12510 ⟨31,by decide⟩).lower ∧ (cell12510 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12510 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12510 ⟨32,by decide⟩).lower ∧ (cell12510 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12510 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12510 ⟨33,by decide⟩).lower ∧ (cell12510 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12510 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12510 ⟨34,by decide⟩).lower ∧ (cell12510 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12510 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12510 ⟨35,by decide⟩).lower ∧ (cell12510 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12510 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12510 ⟨36,by decide⟩).lower ∧ (cell12510 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12510 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12510 ⟨37,by decide⟩).lower ∧ (cell12510 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12510 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12510 ⟨38,by decide⟩).lower ∧ (cell12510 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12510 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12510 ⟨39,by decide⟩).lower ∧ (cell12510 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12510 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12510 ⟨40,by decide⟩).lower ∧ (cell12510 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12510 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12510 ⟨41,by decide⟩).lower ∧ (cell12510 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12510 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12510 ⟨42,by decide⟩).lower ∧ (cell12510 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12510 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12510 ⟨43,by decide⟩).lower ∧ (cell12510 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12510 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12510 ⟨44,by decide⟩).lower ∧ (cell12510 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12510 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12510 ⟨45,by decide⟩).lower ∧ (cell12510 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12510 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12510 ⟨46,by decide⟩).lower ∧ (cell12510 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12510 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12510 ⟨47,by decide⟩).lower ∧ (cell12510 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12510 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12510 ⟨48,by decide⟩).lower ∧ (cell12510 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12510 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12510 ⟨49,by decide⟩).lower ∧ (cell12510 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12510 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12510 ⟨50,by decide⟩).lower ∧ (cell12510 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12510 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12510 ⟨51,by decide⟩).lower ∧ (cell12510 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12510 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12510 ⟨52,by decide⟩).lower ∧ (cell12510 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12510 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12510 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12510 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12510,cell12510,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12510 i).lower ∧
    (cell12510 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12510 i).upper ≤ (0.532 : ℝ) ∧
    (cell12510 i).centre ≤ (0.1 : ℝ) ∧ (cell12510 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12510 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12510 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12510

/-! The local source numeric instances at 12510 have no network premises. -/
namespace BstLean.Part269.N12510
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12510)
open BstLean.Part268 (cell12510)

noncomputable def sourceNumerics12510 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12510 (cell12510 i)
      scalarRow12510.M scalarRow12510.H scalarRow12510.xi := by
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
    energy_allowance := scalarRow12510.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12510]
    centre_nonneg := (scalarRow12510.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12510])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12510
/-! Actual 12511 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12511 ≤ (1.036081074752 : ℝ) := by
  have hr : (111.852581552684 : ℝ) ≤ √(12511 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.852581552684 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12511 12511 (11 / 1000) ≤
    (0.008545954607 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12511) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.852581552684 : ℝ) ≤ √(12511 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12511)
  have hdiv : K / √(12511 : ℝ) ≤ K / 111.852581552684 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.852581552684 ≤ (0.008545954607 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12511.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12511 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12511 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12511 := gPlus_lower 12511
end BstLean.Part269.N12511

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12511
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036081074751 : ℝ) ≤ wn 12511 := by
  have hn : √(12511 : ℝ) ≤ 111.852581552685 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12511 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.852581552685 ≤ 2 / √(12511 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255753065 : ℝ) ≤ rhoBar 12511 BstLean.Part154.csC ∧
    rhoBar 12511 BstLean.Part154.csC ≤ 0.000255753461 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036081074751 : ℝ) / (1.295212 * 12511) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036081074752 : ℝ) / (1.29521 * 12511) := by gcongr
      _ ≤ (0.000255753461 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12511 BstLean.Part154.csC) ≤ 0.001023079254 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12511 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) ≤ 0.000195346359 ∧
    cc1 (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) ≤ 0.000124300156 ∧
    cc2 (rhoBar 12511 BstLean.Part154.csC) ≤ 0.000072157158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12511 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12511 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12511 BstLean.Part154.csC * nuR (rhoBar 12511 BstLean.Part154.csC)) ≤ 0.000511523275 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255753461 : ℝ) * 0.001023079254 := by gcongr
      _ ≤ (0.000511523275 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12511 BstLean.Part154.csC) * nuR (rhoBar 12511 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001023079254 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12511 BstLean.Part154.csC) * rhoBar 12511 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255753461 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255753461 / 2 + 0.399 * 0.001023079254 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195346359 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511523275 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124300156 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255753461 / 1.414213562 := by gcongr
      _ ≤ (0.000072157158 : ℝ) := by norm_num

end BstLean.Part269.N12511

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12511
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) ≤ 1.64796E-7 := by
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12511 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12511 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12511 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195346359 : ℝ) ^ 2 + 0.000124300156 ^ 2 + 3 * 0.000072157158 ^ 2 +
        2 * 0.797885 * 0.000195346359 * 0.000124300156 + 2 * 0.000195346359 * 0.000072157158 +
        4 * 0.797885 * 0.000124300156 * 0.000072157158 := by gcongr
    _ ≤ (1.64796E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12511 BstLean.Part154.csC Θ ≤ 0.002670419873 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12511 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12511 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12511 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036081074752 * 1.64796E-7 / (0.000255753065 : ℝ) := by gcongr
    _ ≤ 0.002670419873 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12511 BstLean.Part154.csC Θ ≤ 0.002963744565 + 0.000674769533 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12511 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12511 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036081074752 : ℝ) * ((2 * Θ * 0.000255753461 +
        (6863 / 10000) * 0.000255753461 * 12511 * 0.001023079254) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002963744565 + 0.000674769533 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12511 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12511 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12511 0.011 Θ ∧ gammaRatio 12511 0.011 Θ ≤ 0.000087921427 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12511 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036081074752 : ℝ) * 0.525 / ((1 - 0.011) * 12511) := by gcongr
      _ ≤ (0.000087921427 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12511 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12511 0.011 Θ) :=
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
    badAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12511 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12511 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12511 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12511 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12511 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12511 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12511 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12511 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12511 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12511 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036081074752 : ℝ) * 12511 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003738163393 + 0.003345189406 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12511

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12511
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12511 BstLean.Part154.csC) (piBar (rhoBar 12511 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12511 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12511 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12511 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12511 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12511 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12511 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12511 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12511 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12511 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12511 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052883574165 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12511) ≤ 0.010676888853 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12511 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036081074752)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010676888853 + 2 * 0.737676 / 12511) := by gcongr
    _ ≤ (0.052883574165 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12511 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12511

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12511
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494892031 : ℝ) ≤ plow 12511 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12511) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000987832)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401970434) : eMP 12511 0.011 xi bn ≤ 0.001206703573 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12511 : ℝ) * (1 - 0.011))) ≤ 0.000596623328 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401970434 / (12511 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596623328 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596623328 : ℝ) + 3.141593 * 0.053000987832 / (12511 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206703573 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000987832)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401970434) : PiBarMP 12511 12 0.011 xi bn ≤ 0.162477022475 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12511 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037442895642 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.235691214645 : ℝ) ≤ √((12511 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.852581552684 : ℝ) ≤ √(12511 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12511) ≤ 0.124560453316 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037442895642 + 0.053000987832 * 1.772454 / (2 * (111.235691214645 : ℝ))) * (1 + 0.001206703573) +
        8 / (12511 * 111.852581552684) + 0.124560453316 := by gcongr
    _ ≤ (0.162477022475 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000987832)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401970434) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283103008254) :
    parallelOracle 12511 0.011 xi bn cd ≤ 0.163483079358 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12511 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12511 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494892031 : ℝ) ≤ plow 12511 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.852581552684 : ℝ) ≤ √(12511 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283103008254 : ℝ) / (2 * 0.560494892031 * 111.852581552684)) * 0.162477022475 +
        0.283103008254 ^ 2 / (2 * 0.560494892031 * 111.852581552684) := by gcongr
    _ ≤ (0.163483079358 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000987832) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401970434)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283103008254) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12511 12511 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494892031 : ℝ) ≤ plow 12511 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.852581552684 : ℝ) ≤ √(12511 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12511 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12511 Θ 1.22 ≤ 0.011855788053 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.852581552684 := by gcongr <;> linarith
      _ ≤ (0.011855788053 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12511 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12511 12511 0.011 ≤ 0.008545954607 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12511 12511 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12511 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12511 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12511 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12511 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163483079358 + 0.011855788053 + (0.008545954607 : ℝ) *
        (1 + 2 * (0.283103008254 + 0.011855788053) / (0.560494892031 * 111.852581552684))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12511]

end BstLean.Part269.N12511

/-! The original eight local profiles supply actual 12511 moment certificates. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12511 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053000987832 ∧
    0 ≤ bN 12511 BstLean.Part154.csC (groupTheta g) ∧ bN 12511 BstLean.Part154.csC (groupTheta g) ≤ 0.001401970434 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12511 12511 0.011
      (momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12511 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12511 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12511 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230219434089 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12511 0.011
      (momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12511 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12511
/-! The actual computed-centre upper energy formula at 12511. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12511

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12511)
open BstLean.Part268 (cell12511)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086062110332
  | 2 => 0.087015849880
  | 3 => 0.087969409087
  | 4 => 0.088924587190
  | 5 => 0.089883546865
  | 6 => 0.090848866400
  | 7 => 0.091823596470
  | 8 => 0.092811321463
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12511 12511 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12511 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12511

/-! Actual upper energy certificates on all 43 source endpoints at 12511. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12511)
open BstLean.Part268 (cell12511)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12511 (gMinus 12511) (1 - (cell12511 i).lower) ≤ 1 ∧
    energyUpper 12511 (gMinus 12511) (BstLean.Part211.gPlus 12511)
      (finiteEnergy 12511 12511 0.011) (1 - (cell12511 i).lower) ≤
      (cell12511 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨10,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨11,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨12,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨13,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨14,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨15,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨16,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨17,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨18,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨19,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨20,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨21,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨22,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨23,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨24,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨25,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨26,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨27,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨28,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨29,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨30,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨31,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨32,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨33,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨34,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨35,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨36,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨37,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨38,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨39,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨40,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨41,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨42,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨43,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨44,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨45,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨46,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨47,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨48,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨49,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨50,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨51,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12511) (by norm_num)
        (q := 1 - (cell12511 ⟨52,by decide⟩).lower)
        (by norm_num [cell12511]) (by norm_num [cell12511])
      exact ⟨E.1,E.2.trans (by norm_num [cell12511])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12511

/-! Source-cell containment and simple scalar guards at 12511. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12511)
open BstLean.Part268 (cell12511)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12511 ⟨10,by decide⟩).lower ∧ (cell12511 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12511 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12511 ⟨11,by decide⟩).lower ∧ (cell12511 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12511 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12511 ⟨12,by decide⟩).lower ∧ (cell12511 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12511 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12511 ⟨13,by decide⟩).lower ∧ (cell12511 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12511 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12511 ⟨14,by decide⟩).lower ∧ (cell12511 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12511 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12511 ⟨15,by decide⟩).lower ∧ (cell12511 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12511 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12511 ⟨16,by decide⟩).lower ∧ (cell12511 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12511 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12511 ⟨17,by decide⟩).lower ∧ (cell12511 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12511 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12511 ⟨18,by decide⟩).lower ∧ (cell12511 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12511 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12511 ⟨19,by decide⟩).lower ∧ (cell12511 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12511 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12511 ⟨20,by decide⟩).lower ∧ (cell12511 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12511 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12511 ⟨21,by decide⟩).lower ∧ (cell12511 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12511 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12511 ⟨22,by decide⟩).lower ∧ (cell12511 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12511 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12511 ⟨23,by decide⟩).lower ∧ (cell12511 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12511 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12511 ⟨24,by decide⟩).lower ∧ (cell12511 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12511 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12511 ⟨25,by decide⟩).lower ∧ (cell12511 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12511 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12511 ⟨26,by decide⟩).lower ∧ (cell12511 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12511 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12511 ⟨27,by decide⟩).lower ∧ (cell12511 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12511 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12511 ⟨28,by decide⟩).lower ∧ (cell12511 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12511 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12511 ⟨29,by decide⟩).lower ∧ (cell12511 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12511 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12511 ⟨30,by decide⟩).lower ∧ (cell12511 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12511 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12511 ⟨31,by decide⟩).lower ∧ (cell12511 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12511 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12511 ⟨32,by decide⟩).lower ∧ (cell12511 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12511 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12511 ⟨33,by decide⟩).lower ∧ (cell12511 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12511 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12511 ⟨34,by decide⟩).lower ∧ (cell12511 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12511 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12511 ⟨35,by decide⟩).lower ∧ (cell12511 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12511 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12511 ⟨36,by decide⟩).lower ∧ (cell12511 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12511 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12511 ⟨37,by decide⟩).lower ∧ (cell12511 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12511 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12511 ⟨38,by decide⟩).lower ∧ (cell12511 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12511 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12511 ⟨39,by decide⟩).lower ∧ (cell12511 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12511 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12511 ⟨40,by decide⟩).lower ∧ (cell12511 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12511 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12511 ⟨41,by decide⟩).lower ∧ (cell12511 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12511 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12511 ⟨42,by decide⟩).lower ∧ (cell12511 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12511 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12511 ⟨43,by decide⟩).lower ∧ (cell12511 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12511 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12511 ⟨44,by decide⟩).lower ∧ (cell12511 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12511 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12511 ⟨45,by decide⟩).lower ∧ (cell12511 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12511 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12511 ⟨46,by decide⟩).lower ∧ (cell12511 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12511 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12511 ⟨47,by decide⟩).lower ∧ (cell12511 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12511 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12511 ⟨48,by decide⟩).lower ∧ (cell12511 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12511 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12511 ⟨49,by decide⟩).lower ∧ (cell12511 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12511 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12511 ⟨50,by decide⟩).lower ∧ (cell12511 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12511 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12511 ⟨51,by decide⟩).lower ∧ (cell12511 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12511 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12511 ⟨52,by decide⟩).lower ∧ (cell12511 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12511 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12511 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12511 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12511,cell12511,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12511 i).lower ∧
    (cell12511 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12511 i).upper ≤ (0.532 : ℝ) ∧
    (cell12511 i).centre ≤ (0.1 : ℝ) ∧ (cell12511 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12511 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12511 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12511

/-! The local source numeric instances at 12511 have no network premises. -/
namespace BstLean.Part269.N12511
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12511)
open BstLean.Part268 (cell12511)

noncomputable def sourceNumerics12511 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12511 (cell12511 i)
      scalarRow12511.M scalarRow12511.H scalarRow12511.xi := by
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
    energy_allowance := scalarRow12511.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12511]
    centre_nonneg := (scalarRow12511.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12511])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12511
/-! Actual 12512 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12512 ≤ (1.036079620088 : ℝ) := by
  have hr : (111.857051632876 : ℝ) ≤ √(12512 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.857051632876 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12512 12512 (11 / 1000) ≤
    (0.008545613087 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12512) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.857051632876 : ℝ) ≤ √(12512 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12512)
  have hdiv : K / √(12512 : ℝ) ≤ K / 111.857051632876 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.857051632876 ≤ (0.008545613087 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12512.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12512 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12512 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12512 := gPlus_lower 12512
end BstLean.Part269.N12512

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12512
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036079620087 : ℝ) ≤ wn 12512 := by
  have hn : √(12512 : ℝ) ≤ 111.857051632877 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12512 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.857051632877 ≤ 2 / √(12512 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255732266 : ℝ) ≤ rhoBar 12512 BstLean.Part154.csC ∧
    rhoBar 12512 BstLean.Part154.csC ≤ 0.000255732662 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036079620087 : ℝ) / (1.295212 * 12512) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036079620088 : ℝ) / (1.29521 * 12512) := by gcongr
      _ ≤ (0.000255732662 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12512 BstLean.Part154.csC) ≤ 0.001022996048 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12512 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) ≤ 0.000195330471 ∧
    cc1 (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) ≤ 0.000124290047 ∧
    cc2 (rhoBar 12512 BstLean.Part154.csC) ≤ 0.000072151290 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12512 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12512 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12512 BstLean.Part154.csC * nuR (rhoBar 12512 BstLean.Part154.csC)) ≤ 0.000511481674 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255732662 : ℝ) * 0.001022996048 := by gcongr
      _ ≤ (0.000511481674 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12512 BstLean.Part154.csC) * nuR (rhoBar 12512 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001022996048 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12512 BstLean.Part154.csC) * rhoBar 12512 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255732662 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255732662 / 2 + 0.399 * 0.001022996048 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195330471 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000511481674 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124290047 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255732662 / 1.414213562 := by gcongr
      _ ≤ (0.000072151290 : ℝ) := by norm_num

end BstLean.Part269.N12512

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12512
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) ≤ 1.64769E-7 := by
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12512 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12512 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12512 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195330471 : ℝ) ^ 2 + 0.000124290047 ^ 2 + 3 * 0.000072151290 ^ 2 +
        2 * 0.797885 * 0.000195330471 * 0.000124290047 + 2 * 0.000195330471 * 0.000072151290 +
        4 * 0.797885 * 0.000124290047 * 0.000072151290 := by gcongr
    _ ≤ (1.64769E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12512 BstLean.Part154.csC Θ ≤ 0.002670195758 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12512 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12512 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12512 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036079620088 * 1.64769E-7 / (0.000255732266 : ℝ) := by gcongr
    _ ≤ 0.002670195758 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12512 BstLean.Part154.csC Θ ≤ 0.002963495213 + 0.000674713711 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12512 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12512 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036079620088 : ℝ) * ((2 * Θ * 0.000255732662 +
        (6863 / 10000) * 0.000255732662 * 12512 * 0.001022996048) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002963495213 + 0.000674713711 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12512 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12512 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12512 0.011 Θ ∧ gammaRatio 12512 0.011 Θ ≤ 0.000087914276 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12512 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036079620088 : ℝ) * 0.525 / ((1 - 0.011) * 12512) := by gcongr
      _ ≤ (0.000087914276 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12512 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12512 0.011 Θ) :=
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
    badAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000774418828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12512 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12512 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12512 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12512 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12512 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12512 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12512 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12512 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12512 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12512 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036079620088 : ℝ) * 12512 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000774418828 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003737914041 + 0.003344909469 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12512

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12512
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12512 BstLean.Part154.csC) (piBar (rhoBar 12512 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12512 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12512 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12512 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12512 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12512 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12512 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12512 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12512 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12512 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12512 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052881437720 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12512) ≤ 0.010676462178 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12512 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036079620088)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010676462178 + 2 * 0.737676 / 12512) := by gcongr
    _ ≤ (0.052881437720 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12512 12 ≤ 0.0015 := by
  exact BstLean.Part269.S6.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12512

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12512
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560494938626 : ℝ) ≤ plow 12512 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12512) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000591513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401852773) : eMP 12512 0.011 xi bn ≤ 0.001206604641 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12512 : ℝ) * (1 - 0.011))) ≤ 0.000596574450 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001401852773 / (12512 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000596574450 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000596574450 : ℝ) + 3.141593 * 0.053000591513 / (12512 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001206604641 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000591513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401852773) : PiBarMP 12512 12 0.011 xi bn ≤ 0.162470447113 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12512 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037441324403 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.240136641411 : ℝ) ≤ √((12512 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.857051632876 : ℝ) ≤ √(12512 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12512) ≤ 0.124555475577 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037441324403 + 0.053000591513 * 1.772454 / (2 * (111.240136641411 : ℝ))) * (1 + 0.001206604641) +
        8 / (12512 * 111.857051632876) + 0.124555475577 := by gcongr
    _ ≤ (0.162470447113 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000591513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401852773) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283100011065) :
    parallelOracle 12512 0.011 xi bn cd ≤ 0.163476431445 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12512 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12512 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560494938626 : ℝ) ≤ plow 12512 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.857051632876 : ℝ) ≤ √(12512 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283100011065 : ℝ) / (2 * 0.560494938626 * 111.857051632876)) * 0.162470447113 +
        0.283100011065 ^ 2 / (2 * 0.560494938626 * 111.857051632876) := by gcongr
    _ ≤ (0.163476431445 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053000591513) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001401852773)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283100011065) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12512 12512 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560494938626 : ℝ) ≤ plow 12512 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.857051632876 : ℝ) ≤ √(12512 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12512 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12512 Θ 1.22 ≤ 0.011855314267 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.857051632876 := by gcongr <;> linarith
      _ ≤ (0.011855314267 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12512 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12512 12512 0.011 ≤ 0.008545613087 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12512 12512 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12512 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12512 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12512 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12512 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163476431445 + 0.011855314267 + (0.008545613087 : ℝ) *
        (1 + 2 * (0.283100011065 + 0.011855314267) / (0.560494938626 * 111.857051632876))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12512]

end BstLean.Part269.N12512

/-! The original eight local profiles supply actual 12512 moment certificates. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12512 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053000591513 ∧
    0 ≤ bN 12512 BstLean.Part154.csC (groupTheta g) ∧ bN 12512 BstLean.Part154.csC (groupTheta g) ≤ 0.001401852773 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12512 12512 0.011
      (momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12512 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12512 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12512 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230218573345 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12512 0.011
      (momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12512 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12512
/-! The actual computed-centre upper energy formula at 12512. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12512

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12512)
open BstLean.Part268 (cell12512)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086058968522
  | 2 => 0.087012644986
  | 3 => 0.087966131064
  | 4 => 0.088921223747
  | 5 => 0.089880083073
  | 6 => 0.090845284271
  | 7 => 0.091819874470
  | 8 => 0.092807433987
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12512 12512 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12512 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003740909217 + 0.003348232271 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S6.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S6.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12512

/-! Actual upper energy certificates on all 43 source endpoints at 12512. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12512)
open BstLean.Part268 (cell12512)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12512 (gMinus 12512) (1 - (cell12512 i).lower) ≤ 1 ∧
    energyUpper 12512 (gMinus 12512) (BstLean.Part211.gPlus 12512)
      (finiteEnergy 12512 12512 0.011) (1 - (cell12512 i).lower) ≤
      (cell12512 i).energy := by
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
      have E := BstLean.Part269.S6.uniformEnergy10 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨10,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy11 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨11,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy12 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨12,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy13 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨13,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy14 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨14,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy15 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨15,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy16 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨16,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy17 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨17,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy18 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨18,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy19 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨19,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy20 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨20,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy21 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨21,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy22 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨22,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy23 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨23,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy24 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨24,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy25 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨25,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy26 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨26,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy27 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨27,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy28 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨28,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy29 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨29,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy30 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨30,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy31 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨31,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy32 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨32,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy33 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨33,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy34 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨34,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy35 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨35,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy36 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨36,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy37 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨37,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy38 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨38,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy39 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨39,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy40 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨40,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy41 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨41,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy42 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨42,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy43 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨43,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy44 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨44,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy45 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨45,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy46 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨46,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy47 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨47,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy48 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨48,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy49 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨49,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy50 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨50,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy51 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨51,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S6.uniformEnergy52 (n := 12512) (by norm_num)
        (q := 1 - (cell12512 ⟨52,by decide⟩).lower)
        (by norm_num [cell12512]) (by norm_num [cell12512])
      exact ⟨E.1,E.2.trans (by norm_num [cell12512])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12512

/-! Source-cell containment and simple scalar guards at 12512. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12512)
open BstLean.Part268 (cell12512)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12512 ⟨10,by decide⟩).lower ∧ (cell12512 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12512 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12512 ⟨11,by decide⟩).lower ∧ (cell12512 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12512 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12512 ⟨12,by decide⟩).lower ∧ (cell12512 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12512 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12512 ⟨13,by decide⟩).lower ∧ (cell12512 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12512 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12512 ⟨14,by decide⟩).lower ∧ (cell12512 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12512 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12512 ⟨15,by decide⟩).lower ∧ (cell12512 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12512 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12512 ⟨16,by decide⟩).lower ∧ (cell12512 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12512 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12512 ⟨17,by decide⟩).lower ∧ (cell12512 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12512 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12512 ⟨18,by decide⟩).lower ∧ (cell12512 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12512 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12512 ⟨19,by decide⟩).lower ∧ (cell12512 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12512 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12512 ⟨20,by decide⟩).lower ∧ (cell12512 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12512 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12512 ⟨21,by decide⟩).lower ∧ (cell12512 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12512 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12512 ⟨22,by decide⟩).lower ∧ (cell12512 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12512 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12512 ⟨23,by decide⟩).lower ∧ (cell12512 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12512 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12512 ⟨24,by decide⟩).lower ∧ (cell12512 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12512 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12512 ⟨25,by decide⟩).lower ∧ (cell12512 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12512 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12512 ⟨26,by decide⟩).lower ∧ (cell12512 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12512 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12512 ⟨27,by decide⟩).lower ∧ (cell12512 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12512 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12512 ⟨28,by decide⟩).lower ∧ (cell12512 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12512 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12512 ⟨29,by decide⟩).lower ∧ (cell12512 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12512 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12512 ⟨30,by decide⟩).lower ∧ (cell12512 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12512 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12512 ⟨31,by decide⟩).lower ∧ (cell12512 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12512 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12512 ⟨32,by decide⟩).lower ∧ (cell12512 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12512 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12512 ⟨33,by decide⟩).lower ∧ (cell12512 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12512 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12512 ⟨34,by decide⟩).lower ∧ (cell12512 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12512 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12512 ⟨35,by decide⟩).lower ∧ (cell12512 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12512 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12512 ⟨36,by decide⟩).lower ∧ (cell12512 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12512 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12512 ⟨37,by decide⟩).lower ∧ (cell12512 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12512 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12512 ⟨38,by decide⟩).lower ∧ (cell12512 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12512 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12512 ⟨39,by decide⟩).lower ∧ (cell12512 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12512 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12512 ⟨40,by decide⟩).lower ∧ (cell12512 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12512 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12512 ⟨41,by decide⟩).lower ∧ (cell12512 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12512 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12512 ⟨42,by decide⟩).lower ∧ (cell12512 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12512 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12512 ⟨43,by decide⟩).lower ∧ (cell12512 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12512 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12512 ⟨44,by decide⟩).lower ∧ (cell12512 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12512 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12512 ⟨45,by decide⟩).lower ∧ (cell12512 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12512 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12512 ⟨46,by decide⟩).lower ∧ (cell12512 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12512 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12512 ⟨47,by decide⟩).lower ∧ (cell12512 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12512 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12512 ⟨48,by decide⟩).lower ∧ (cell12512 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12512 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12512 ⟨49,by decide⟩).lower ∧ (cell12512 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12512 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12512 ⟨50,by decide⟩).lower ∧ (cell12512 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12512 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12512 ⟨51,by decide⟩).lower ∧ (cell12512 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12512 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12512 ⟨52,by decide⟩).lower ∧ (cell12512 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12512 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12512 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12512 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12512,cell12512,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12512 i).lower ∧
    (cell12512 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12512 i).upper ≤ (0.532 : ℝ) ∧
    (cell12512 i).centre ≤ (0.1 : ℝ) ∧ (cell12512 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12512 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12512 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12512

/-! The local source numeric instances at 12512 have no network premises. -/
namespace BstLean.Part269.N12512
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12512)
open BstLean.Part268 (cell12512)

noncomputable def sourceNumerics12512 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12512 (cell12512 i)
      scalarRow12512.M scalarRow12512.H scalarRow12512.xi := by
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
    energy_allowance := scalarRow12512.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12512]
    centre_nonneg := (scalarRow12512.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D6.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12512])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12512