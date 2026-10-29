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
import BstLean.Part269Direction34
import BstLean.Part269Shared34
import BstLean.Part269Finite
import BstLean.Part269N13224Source
import BstLean.Part269Rows34
import BstLean.Part269Source
/-! Actual 13213 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13213 ≤ (1.035101131991 : ℝ) := by
  have hr : (114.947814246291 : ℝ) ≤ √(13213 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.947814246291 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13213 13213 (11 / 1000) ≤
    (0.008315833517 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13213) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.947814246291 : ℝ) ≤ √(13213 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13213)
  have hdiv : K / √(13213 : ℝ) ≤ K / 114.947814246291 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.947814246291 ≤ (0.008315833517 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13213.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13213 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13213 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13213 := gPlus_lower 13213
end BstLean.Part269.N13213

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13213
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035101131990 : ℝ) ≤ wn 13213 := by
  have hn : √(13213 : ℝ) ≤ 114.947814246292 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13213 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.947814246292 ≤ 2 / √(13213 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241935991 : ℝ) ≤ rhoBar 13213 BstLean.Part154.csC ∧
    rhoBar 13213 BstLean.Part154.csC ≤ 0.000241936365 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035101131990 : ℝ) / (1.295212 * 13213) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035101131991 : ℝ) / (1.29521 * 13213) := by gcongr
      _ ≤ (0.000241936365 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13213 BstLean.Part154.csC) ≤ 0.000967803994 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13213 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) ≤ 0.000184792288 ∧
    cc1 (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) ≤ 0.000117584630 ∧
    cc2 (rhoBar 13213 BstLean.Part154.csC) ≤ 0.000068258863 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13213 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13213 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13213 BstLean.Part154.csC * nuR (rhoBar 13213 BstLean.Part154.csC)) ≤ 0.000483887364 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241936365 : ℝ) * 0.000967803994 := by gcongr
      _ ≤ (0.000483887364 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13213 BstLean.Part154.csC) * nuR (rhoBar 13213 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967803994 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13213 BstLean.Part154.csC) * rhoBar 13213 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241936365 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241936365 / 2 + 0.399 * 0.000967803994 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184792288 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483887364 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117584630 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241936365 / 1.414213562 := by gcongr
      _ ≤ (0.000068258863 : ℝ) := by norm_num

end BstLean.Part269.N13213

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13213
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) ≤ 1.47470E-7 := by
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13213 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13213 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13213 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184792288 : ℝ) ^ 2 + 0.000117584630 ^ 2 + 3 * 0.000068258863 ^ 2 +
        2 * 0.797885 * 0.000184792288 * 0.000117584630 + 2 * 0.000184792288 * 0.000068258863 +
        4 * 0.797885 * 0.000117584630 * 0.000068258863 := by gcongr
    _ ≤ (1.47470E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13213 BstLean.Part154.csC Θ ≤ 0.002523747927 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13213 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13213 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13213 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035101131991 * 1.47470E-7 / (0.000241935991 : ℝ) := by gcongr
    _ ≤ 0.002523747927 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13213 BstLean.Part154.csC Θ ≤ 0.002798317496 + 0.000637711340 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13213 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13213 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035101131991 : ℝ) * ((2 * Θ * 0.000241936365 +
        (6863 / 10000) * 0.000241936365 * 13213 * 0.000967803994) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002798317496 + 0.000637711340 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13213 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13213 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13213 0.011 Θ ∧ gammaRatio 13213 0.011 Θ ≤ 0.000083171466 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13213 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035101131991 : ℝ) * 0.525 / ((1 - 0.011) * 13213) := by gcongr
      _ ≤ (0.000083171466 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13213 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13213 0.011 Θ) :=
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
    badAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13213 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13213 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13213 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13213 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13213 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13213 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13213 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13213 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13213 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13213 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035101131991 : ℝ) * 13213 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003115888262 + 0.003161459267 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13213

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13213
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13213 BstLean.Part154.csC) (piBar (rhoBar 13213 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13213 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13213 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13213 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13213 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13213 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13213 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13213 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13213 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13213 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13213 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051444425771 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13213) ≤ 0.010389389211 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13213 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035101131991)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010389389211 + 2 * 0.737676 / 13213) := by gcongr
    _ ≤ (0.051444425771 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13213 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13213

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13213
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525866949 : ℝ) ≤ plow 13213 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13213) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282254378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324967662) : eMP 13213 0.011 xi bn ≤ 0.001141347678 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13213 : ℝ) * (1 - 0.011))) ≤ 0.000564389255 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324967662 / (13213 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564389255 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564389255 : ℝ) + 3.141593 * 0.052282254378 / (13213 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141347678 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282254378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324967662) : PiBarMP 13213 12 0.011 xi bn ≤ 0.158059080901 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13213 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036400105248 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.313853053774 : ℝ) ≤ √((13213 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.947814246291 : ℝ) ≤ √(13213 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13213) ≤ 0.121206378339 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036400105248 + 0.052282254378 * 1.772454 / (2 * (114.313853053774 : ℝ))) * (1 + 0.001141347678) +
        8 / (13213 * 114.947814246291) + 0.121206378339 := by gcongr
    _ ≤ (0.158059080901 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282254378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324967662) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280097556907) :
    parallelOracle 13213 0.011 xi bn cd ≤ 0.159011465457 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13213 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13213 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525866949 : ℝ) ≤ plow 13213 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.947814246291 : ℝ) ≤ √(13213 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280097556907 : ℝ) / (2 * 0.560525866949 * 114.947814246291)) * 0.158059080901 +
        0.280097556907 ^ 2 / (2 * 0.560525866949 * 114.947814246291) := by gcongr
    _ ≤ (0.159011465457 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052282254378) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324967662)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280097556907) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13213 13213 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525866949 : ℝ) ≤ plow 13213 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.947814246291 : ℝ) ≤ √(13213 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13213 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13213 Θ 1.22 ≤ 0.011536543855 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.947814246291 := by gcongr <;> linarith
      _ ≤ (0.011536543855 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13213 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13213 13213 0.011 ≤ 0.008315833517 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13213 13213 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13213 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13213 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13213 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13213 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159011465457 + 0.011536543855 + (0.008315833517 : ℝ) *
        (1 + 2 * (0.280097556907 + 0.011536543855) / (0.560525866949 * 114.947814246291))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13213]

end BstLean.Part269.N13213

/-! The original eight local profiles supply actual 13213 moment certificates. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13213 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052282254378 ∧
    0 ≤ bN 13213 BstLean.Part154.csC (groupTheta g) ∧ bN 13213 BstLean.Part154.csC (groupTheta g) ≤ 0.001324967662 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13213 13213 0.011
      (momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13213 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13213 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13213 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228653131136 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13213 0.011
      (momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13213 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13213
/-! The actual computed-centre upper energy formula at 13213. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13213

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13213)
open BstLean.Part268 (cell13213)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084119544001
  | 2 => 0.085041447598
  | 3 => 0.085958582751
  | 4 => 0.086871681441
  | 5 => 0.087781648036
  | 6 => 0.088689587168
  | 7 => 0.089596834686
  | 8 => 0.090504991790
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13213 13213 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13213 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13213

/-! Actual upper energy certificates on all 43 source endpoints at 13213. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13213)
open BstLean.Part268 (cell13213)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13213 (gMinus 13213) (1 - (cell13213 i).lower) ≤ 1 ∧
    energyUpper 13213 (gMinus 13213) (BstLean.Part211.gPlus 13213)
      (finiteEnergy 13213 13213 0.011) (1 - (cell13213 i).lower) ≤
      (cell13213 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨10,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨11,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨12,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨13,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨14,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨15,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨16,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨17,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨18,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨19,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨20,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨21,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨22,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨23,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨24,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨25,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨26,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨27,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨28,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨29,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨30,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨31,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨32,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨33,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨34,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨35,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨36,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨37,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨38,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨39,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨40,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨41,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨42,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨43,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨44,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨45,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨46,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨47,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨48,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨49,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨50,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨51,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13213) (by norm_num)
        (q := 1 - (cell13213 ⟨52,by decide⟩).lower)
        (by norm_num [cell13213]) (by norm_num [cell13213])
      exact ⟨E.1,E.2.trans (by norm_num [cell13213])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13213

/-! Source-cell containment and simple scalar guards at 13213. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13213)
open BstLean.Part268 (cell13213)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13213 ⟨10,by decide⟩).lower ∧ (cell13213 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13213 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13213 ⟨11,by decide⟩).lower ∧ (cell13213 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13213 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13213 ⟨12,by decide⟩).lower ∧ (cell13213 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13213 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13213 ⟨13,by decide⟩).lower ∧ (cell13213 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13213 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13213 ⟨14,by decide⟩).lower ∧ (cell13213 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13213 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13213 ⟨15,by decide⟩).lower ∧ (cell13213 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13213 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13213 ⟨16,by decide⟩).lower ∧ (cell13213 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13213 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13213 ⟨17,by decide⟩).lower ∧ (cell13213 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13213 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13213 ⟨18,by decide⟩).lower ∧ (cell13213 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13213 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13213 ⟨19,by decide⟩).lower ∧ (cell13213 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13213 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13213 ⟨20,by decide⟩).lower ∧ (cell13213 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13213 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13213 ⟨21,by decide⟩).lower ∧ (cell13213 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13213 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13213 ⟨22,by decide⟩).lower ∧ (cell13213 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13213 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13213 ⟨23,by decide⟩).lower ∧ (cell13213 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13213 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13213 ⟨24,by decide⟩).lower ∧ (cell13213 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13213 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13213 ⟨25,by decide⟩).lower ∧ (cell13213 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13213 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13213 ⟨26,by decide⟩).lower ∧ (cell13213 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13213 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13213 ⟨27,by decide⟩).lower ∧ (cell13213 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13213 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13213 ⟨28,by decide⟩).lower ∧ (cell13213 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13213 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13213 ⟨29,by decide⟩).lower ∧ (cell13213 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13213 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13213 ⟨30,by decide⟩).lower ∧ (cell13213 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13213 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13213 ⟨31,by decide⟩).lower ∧ (cell13213 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13213 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13213 ⟨32,by decide⟩).lower ∧ (cell13213 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13213 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13213 ⟨33,by decide⟩).lower ∧ (cell13213 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13213 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13213 ⟨34,by decide⟩).lower ∧ (cell13213 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13213 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13213 ⟨35,by decide⟩).lower ∧ (cell13213 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13213 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13213 ⟨36,by decide⟩).lower ∧ (cell13213 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13213 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13213 ⟨37,by decide⟩).lower ∧ (cell13213 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13213 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13213 ⟨38,by decide⟩).lower ∧ (cell13213 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13213 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13213 ⟨39,by decide⟩).lower ∧ (cell13213 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13213 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13213 ⟨40,by decide⟩).lower ∧ (cell13213 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13213 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13213 ⟨41,by decide⟩).lower ∧ (cell13213 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13213 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13213 ⟨42,by decide⟩).lower ∧ (cell13213 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13213 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13213 ⟨43,by decide⟩).lower ∧ (cell13213 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13213 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13213 ⟨44,by decide⟩).lower ∧ (cell13213 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13213 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13213 ⟨45,by decide⟩).lower ∧ (cell13213 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13213 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13213 ⟨46,by decide⟩).lower ∧ (cell13213 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13213 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13213 ⟨47,by decide⟩).lower ∧ (cell13213 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13213 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13213 ⟨48,by decide⟩).lower ∧ (cell13213 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13213 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13213 ⟨49,by decide⟩).lower ∧ (cell13213 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13213 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13213 ⟨50,by decide⟩).lower ∧ (cell13213 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13213 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13213 ⟨51,by decide⟩).lower ∧ (cell13213 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13213 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13213 ⟨52,by decide⟩).lower ∧ (cell13213 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13213 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13213 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13213 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13213,cell13213,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13213 i).lower ∧
    (cell13213 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13213 i).upper ≤ (0.532 : ℝ) ∧
    (cell13213 i).centre ≤ (0.1 : ℝ) ∧ (cell13213 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13213 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13213 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13213

/-! The local source numeric instances at 13213 have no network premises. -/
namespace BstLean.Part269.N13213
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13213)
open BstLean.Part268 (cell13213)

noncomputable def sourceNumerics13213 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13213 (cell13213 i)
      scalarRow13213.M scalarRow13213.H scalarRow13213.xi := by
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
    energy_allowance := scalarRow13213.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13213]
    centre_nonneg := (scalarRow13213.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13213])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13213
/-! Actual 13214 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13214 ≤ (1.035099792331 : ℝ) := by
  have hr : (114.952163963972 : ℝ) ≤ √(13214 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.952163963972 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13214 13214 (11 / 1000) ≤
    (0.008315518849 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13214) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.952163963972 : ℝ) ≤ √(13214 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13214)
  have hdiv : K / √(13214 : ℝ) ≤ K / 114.952163963972 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.952163963972 ≤ (0.008315518849 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13214.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13214 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13214 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13214 := gPlus_lower 13214
end BstLean.Part269.N13214

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13214
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035099792330 : ℝ) ≤ wn 13214 := by
  have hn : √(13214 : ℝ) ≤ 114.952163963973 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13214 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.952163963973 ≤ 2 / √(13214 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241917369 : ℝ) ≤ rhoBar 13214 BstLean.Part154.csC ∧
    rhoBar 13214 BstLean.Part154.csC ≤ 0.000241917743 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035099792330 : ℝ) / (1.295212 * 13214) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035099792331 : ℝ) / (1.29521 * 13214) := by gcongr
      _ ≤ (0.000241917743 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13214 BstLean.Part154.csC) ≤ 0.000967729497 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13214 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) ≤ 0.000184778064 ∧
    cc1 (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) ≤ 0.000117575579 ∧
    cc2 (rhoBar 13214 BstLean.Part154.csC) ≤ 0.000068253609 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13214 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13214 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13214 BstLean.Part154.csC * nuR (rhoBar 13214 BstLean.Part154.csC)) ≤ 0.000483850118 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241917743 : ℝ) * 0.000967729497 := by gcongr
      _ ≤ (0.000483850118 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13214 BstLean.Part154.csC) * nuR (rhoBar 13214 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967729497 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13214 BstLean.Part154.csC) * rhoBar 13214 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241917743 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241917743 / 2 + 0.399 * 0.000967729497 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184778064 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483850118 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117575579 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241917743 / 1.414213562 := by gcongr
      _ ≤ (0.000068253609 : ℝ) := by norm_num

end BstLean.Part269.N13214

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13214
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) ≤ 1.47447E-7 := by
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13214 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13214 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13214 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184778064 : ℝ) ^ 2 + 0.000117575579 ^ 2 + 3 * 0.000068253609 ^ 2 +
        2 * 0.797885 * 0.000184778064 * 0.000117575579 + 2 * 0.000184778064 * 0.000068253609 +
        4 * 0.797885 * 0.000117575579 * 0.000068253609 := by gcongr
    _ ≤ (1.47447E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13214 BstLean.Part154.csC Θ ≤ 0.002523545287 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13214 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13214 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13214 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035099792331 * 1.47447E-7 / (0.000241917369 : ℝ) := by gcongr
    _ ≤ 0.002523545287 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13214 BstLean.Part154.csC Θ ≤ 0.002798094854 + 0.000637661430 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13214 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13214 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035099792331 : ℝ) * ((2 * Θ * 0.000241917743 +
        (6863 / 10000) * 0.000241917743 * 13214 * 0.000967729497) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002798094854 + 0.000637661430 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13214 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13214 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13214 0.011 Θ ∧ gammaRatio 13214 0.011 Θ ≤ 0.000083165065 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13214 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035099792331 : ℝ) * 0.525 / ((1 - 0.011) * 13214) := by gcongr
      _ ≤ (0.000083165065 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13214 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13214 0.011 Θ) :=
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
    badAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13214 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13214 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13214 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13214 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13214 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13214 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13214 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13214 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13214 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13214 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035099792331 : ℝ) * 13214 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003115665620 + 0.003161206717 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13214

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13214
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13214 BstLean.Part154.csC) (piBar (rhoBar 13214 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13214 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13214 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13214 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13214 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13214 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13214 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13214 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13214 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13214 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13214 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051442458448 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13214) ≤ 0.010388996083 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13214 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035099792331)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010388996083 + 2 * 0.737676 / 13214) := by gcongr
    _ ≤ (0.051442458448 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13214 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13214

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13214
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525908725 : ℝ) ≤ plow 13214 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13214) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281899147)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324861276) : eMP 13214 0.011 xi bn ≤ 0.001141258613 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13214 : ℝ) * (1 - 0.011))) ≤ 0.000564345241 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324861276 / (13214 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564345241 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564345241 : ℝ) + 3.141593 * 0.052281899147 / (13214 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141258613 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281899147)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324861276) : PiBarMP 13214 12 0.011 xi bn ≤ 0.158053009500 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13214 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036398643876 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.318178781854 : ℝ) ≤ √((13214 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.952163963972 : ℝ) ≤ √(13214 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13214) ≤ 0.121201791966 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036398643876 + 0.052281899147 * 1.772454 / (2 * (114.318178781854 : ℝ))) * (1 + 0.001141258613) +
        8 / (13214 * 114.952163963972) + 0.121201791966 := by gcongr
    _ ≤ (0.158053009500 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281899147)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324861276) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280094812792) :
    parallelOracle 13214 0.011 xi bn cd ≤ 0.159005329457 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13214 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13214 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525908725 : ℝ) ≤ plow 13214 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.952163963972 : ℝ) ≤ √(13214 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280094812792 : ℝ) / (2 * 0.560525908725 * 114.952163963972)) * 0.158053009500 +
        0.280094812792 ^ 2 / (2 * 0.560525908725 * 114.952163963972) := by gcongr
    _ ≤ (0.159005329457 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281899147) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324861276)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280094812792) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13214 13214 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525908725 : ℝ) ≤ plow 13214 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.952163963972 : ℝ) ≤ √(13214 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13214 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13214 Θ 1.22 ≤ 0.011536107319 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.952163963972 := by gcongr <;> linarith
      _ ≤ (0.011536107319 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13214 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13214 13214 0.011 ≤ 0.008315518849 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13214 13214 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13214 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13214 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13214 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13214 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159005329457 + 0.011536107319 + (0.008315518849 : ℝ) *
        (1 + 2 * (0.280094812792 + 0.011536107319) / (0.560525908725 * 114.952163963972))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13214]

end BstLean.Part269.N13214

/-! The original eight local profiles supply actual 13214 moment certificates. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13214 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052281899147 ∧
    0 ≤ bN 13214 BstLean.Part154.csC (groupTheta g) ∧ bN 13214 BstLean.Part154.csC (groupTheta g) ≤ 0.001324861276 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13214 13214 0.011
      (momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13214 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13214 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13214 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228652354344 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13214 0.011
      (momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13214 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13214
/-! The actual computed-centre upper energy formula at 13214. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13214

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13214)
open BstLean.Part268 (cell13214)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084117082225
  | 2 => 0.085038956588
  | 3 => 0.085956058532
  | 4 => 0.086869119079
  | 5 => 0.087779041454
  | 6 => 0.088686928943
  | 7 => 0.089594115813
  | 8 => 0.090502201423
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13214 13214 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13214 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13214

/-! Actual upper energy certificates on all 43 source endpoints at 13214. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13214)
open BstLean.Part268 (cell13214)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13214 (gMinus 13214) (1 - (cell13214 i).lower) ≤ 1 ∧
    energyUpper 13214 (gMinus 13214) (BstLean.Part211.gPlus 13214)
      (finiteEnergy 13214 13214 0.011) (1 - (cell13214 i).lower) ≤
      (cell13214 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨10,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨11,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨12,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨13,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨14,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨15,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨16,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨17,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨18,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨19,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨20,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨21,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨22,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨23,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨24,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨25,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨26,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨27,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨28,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨29,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨30,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨31,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨32,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨33,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨34,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨35,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨36,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨37,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨38,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨39,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨40,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨41,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨42,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨43,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨44,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨45,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨46,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨47,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨48,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨49,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨50,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨51,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13214) (by norm_num)
        (q := 1 - (cell13214 ⟨52,by decide⟩).lower)
        (by norm_num [cell13214]) (by norm_num [cell13214])
      exact ⟨E.1,E.2.trans (by norm_num [cell13214])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13214

/-! Source-cell containment and simple scalar guards at 13214. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13214)
open BstLean.Part268 (cell13214)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13214 ⟨10,by decide⟩).lower ∧ (cell13214 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13214 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13214 ⟨11,by decide⟩).lower ∧ (cell13214 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13214 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13214 ⟨12,by decide⟩).lower ∧ (cell13214 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13214 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13214 ⟨13,by decide⟩).lower ∧ (cell13214 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13214 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13214 ⟨14,by decide⟩).lower ∧ (cell13214 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13214 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13214 ⟨15,by decide⟩).lower ∧ (cell13214 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13214 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13214 ⟨16,by decide⟩).lower ∧ (cell13214 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13214 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13214 ⟨17,by decide⟩).lower ∧ (cell13214 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13214 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13214 ⟨18,by decide⟩).lower ∧ (cell13214 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13214 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13214 ⟨19,by decide⟩).lower ∧ (cell13214 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13214 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13214 ⟨20,by decide⟩).lower ∧ (cell13214 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13214 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13214 ⟨21,by decide⟩).lower ∧ (cell13214 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13214 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13214 ⟨22,by decide⟩).lower ∧ (cell13214 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13214 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13214 ⟨23,by decide⟩).lower ∧ (cell13214 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13214 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13214 ⟨24,by decide⟩).lower ∧ (cell13214 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13214 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13214 ⟨25,by decide⟩).lower ∧ (cell13214 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13214 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13214 ⟨26,by decide⟩).lower ∧ (cell13214 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13214 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13214 ⟨27,by decide⟩).lower ∧ (cell13214 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13214 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13214 ⟨28,by decide⟩).lower ∧ (cell13214 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13214 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13214 ⟨29,by decide⟩).lower ∧ (cell13214 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13214 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13214 ⟨30,by decide⟩).lower ∧ (cell13214 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13214 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13214 ⟨31,by decide⟩).lower ∧ (cell13214 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13214 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13214 ⟨32,by decide⟩).lower ∧ (cell13214 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13214 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13214 ⟨33,by decide⟩).lower ∧ (cell13214 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13214 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13214 ⟨34,by decide⟩).lower ∧ (cell13214 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13214 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13214 ⟨35,by decide⟩).lower ∧ (cell13214 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13214 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13214 ⟨36,by decide⟩).lower ∧ (cell13214 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13214 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13214 ⟨37,by decide⟩).lower ∧ (cell13214 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13214 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13214 ⟨38,by decide⟩).lower ∧ (cell13214 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13214 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13214 ⟨39,by decide⟩).lower ∧ (cell13214 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13214 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13214 ⟨40,by decide⟩).lower ∧ (cell13214 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13214 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13214 ⟨41,by decide⟩).lower ∧ (cell13214 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13214 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13214 ⟨42,by decide⟩).lower ∧ (cell13214 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13214 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13214 ⟨43,by decide⟩).lower ∧ (cell13214 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13214 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13214 ⟨44,by decide⟩).lower ∧ (cell13214 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13214 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13214 ⟨45,by decide⟩).lower ∧ (cell13214 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13214 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13214 ⟨46,by decide⟩).lower ∧ (cell13214 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13214 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13214 ⟨47,by decide⟩).lower ∧ (cell13214 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13214 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13214 ⟨48,by decide⟩).lower ∧ (cell13214 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13214 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13214 ⟨49,by decide⟩).lower ∧ (cell13214 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13214 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13214 ⟨50,by decide⟩).lower ∧ (cell13214 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13214 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13214 ⟨51,by decide⟩).lower ∧ (cell13214 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13214 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13214 ⟨52,by decide⟩).lower ∧ (cell13214 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13214 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13214 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13214 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13214,cell13214,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13214 i).lower ∧
    (cell13214 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13214 i).upper ≤ (0.532 : ℝ) ∧
    (cell13214 i).centre ≤ (0.1 : ℝ) ∧ (cell13214 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13214 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13214 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13214

/-! The local source numeric instances at 13214 have no network premises. -/
namespace BstLean.Part269.N13214
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13214)
open BstLean.Part268 (cell13214)

noncomputable def sourceNumerics13214 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13214 (cell13214 i)
      scalarRow13214.M scalarRow13214.H scalarRow13214.xi := by
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
    energy_allowance := scalarRow13214.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13214]
    centre_nonneg := (scalarRow13214.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13214])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13214
/-! Actual 13215 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13215 ≤ (1.035098452824 : ℝ) := by
  have hr : (114.956513517068 : ℝ) ≤ √(13215 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.956513517068 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13215 13215 (11 / 1000) ≤
    (0.008315204216 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13215) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.956513517068 : ℝ) ≤ √(13215 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13215)
  have hdiv : K / √(13215 : ℝ) ≤ K / 114.956513517068 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.956513517068 ≤ (0.008315204216 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13215.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13215 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13215 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13215 := gPlus_lower 13215
end BstLean.Part269.N13215

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13215
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035098452823 : ℝ) ≤ wn 13215 := by
  have hn : √(13215 : ℝ) ≤ 114.956513517069 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13215 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.956513517069 ≤ 2 / √(13215 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241898749 : ℝ) ≤ rhoBar 13215 BstLean.Part154.csC ∧
    rhoBar 13215 BstLean.Part154.csC ≤ 0.000241899124 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035098452823 : ℝ) / (1.295212 * 13215) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035098452824 : ℝ) / (1.29521 * 13215) := by gcongr
      _ ≤ (0.000241899124 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13215 BstLean.Part154.csC) ≤ 0.000967655012 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13215 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) ≤ 0.000184763842 ∧
    cc1 (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) ≤ 0.000117566530 ∧
    cc2 (rhoBar 13215 BstLean.Part154.csC) ≤ 0.000068248356 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13215 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13215 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13215 BstLean.Part154.csC * nuR (rhoBar 13215 BstLean.Part154.csC)) ≤ 0.000483812877 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241899124 : ℝ) * 0.000967655012 := by gcongr
      _ ≤ (0.000483812877 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13215 BstLean.Part154.csC) * nuR (rhoBar 13215 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967655012 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13215 BstLean.Part154.csC) * rhoBar 13215 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241899124 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241899124 / 2 + 0.399 * 0.000967655012 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184763842 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483812877 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117566530 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241899124 / 1.414213562 := by gcongr
      _ ≤ (0.000068248356 : ℝ) := by norm_num

end BstLean.Part269.N13215

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13215
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) ≤ 1.47425E-7 := by
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13215 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13215 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13215 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184763842 : ℝ) ^ 2 + 0.000117566530 ^ 2 + 3 * 0.000068248356 ^ 2 +
        2 * 0.797885 * 0.000184763842 * 0.000117566530 + 2 * 0.000184763842 * 0.000068248356 +
        4 * 0.797885 * 0.000117566530 * 0.000068248356 := by gcongr
    _ ≤ (1.47425E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13215 BstLean.Part154.csC Θ ≤ 0.002523359713 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13215 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13215 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13215 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035098452824 * 1.47425E-7 / (0.000241898749 : ℝ) := by gcongr
    _ ≤ 0.002523359713 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13215 BstLean.Part154.csC Θ ≤ 0.002797872250 + 0.000637611527 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13215 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13215 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035098452824 : ℝ) * ((2 * Θ * 0.000241899124 +
        (6863 / 10000) * 0.000241899124 * 13215 * 0.000967655012) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002797872250 + 0.000637611527 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13215 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13215 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13215 0.011 Θ ∧ gammaRatio 13215 0.011 Θ ≤ 0.000083158664 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13215 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035098452824 : ℝ) * 0.525 / ((1 - 0.011) * 13215) := by gcongr
      _ ≤ (0.000083158664 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13215 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13215 0.011 Θ) :=
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
    badAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13215 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13215 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13215 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13215 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13215 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13215 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13215 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13215 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13215 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13215 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035098452824 : ℝ) * 13215 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003115443016 + 0.003160971240 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13215

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13215
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13215 BstLean.Part154.csC) (piBar (rhoBar 13215 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13215 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13215 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13215 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13215 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13215 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13215 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13215 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13215 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13215 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13215 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051440491347 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13215) ≤ 0.010388602999 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13215 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035098452824)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010388602999 + 2 * 0.737676 / 13215) := by gcongr
    _ ≤ (0.051440491347 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13215 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13215

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13215
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525950495 : ℝ) ≤ plow 13215 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13215) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281552917)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324763850) : eMP 13215 0.011 xi bn ≤ 0.001141173373 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13215 : ℝ) * (1 - 0.011))) ≤ 0.000564303138 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324763850 / (13215 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564303138 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564303138 : ℝ) + 3.141593 * 0.052281552917 / (13215 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141173373 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281552917)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324763850) : PiBarMP 13215 12 0.011 xi bn ≤ 0.158047062002 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13215 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036397305533 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.322504346257 : ℝ) ≤ √((13215 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.956513517068 : ℝ) ≤ √(13215 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13215) ≤ 0.121197206113 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036397305533 + 0.052281552917 * 1.772454 / (2 * (114.322504346257 : ℝ))) * (1 + 0.001141173373) +
        8 / (13215 * 114.956513517068) + 0.121197206113 := by gcongr
    _ ≤ (0.158047062002 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281552917)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324763850) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280092088580) :
    parallelOracle 13215 0.011 xi bn cd ≤ 0.158999317746 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13215 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13215 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525950495 : ℝ) ≤ plow 13215 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.956513517068 : ℝ) ≤ √(13215 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280092088580 : ℝ) / (2 * 0.560525950495 * 114.956513517068)) * 0.158047062002 +
        0.280092088580 ^ 2 / (2 * 0.560525950495 * 114.956513517068) := by gcongr
    _ ≤ (0.158999317746 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281552917) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324763850)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280092088580) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13215 13215 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525950495 : ℝ) ≤ plow 13215 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.956513517068 : ℝ) ≤ √(13215 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13215 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13215 Θ 1.22 ≤ 0.011535670833 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.956513517068 := by gcongr <;> linarith
      _ ≤ (0.011535670833 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13215 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13215 13215 0.011 ≤ 0.008315204216 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13215 13215 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13215 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13215 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13215 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13215 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158999317746 + 0.011535670833 + (0.008315204216 : ℝ) *
        (1 + 2 * (0.280092088580 + 0.011535670833) / (0.560525950495 * 114.956513517068))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13215]

end BstLean.Part269.N13215

/-! The original eight local profiles supply actual 13215 moment certificates. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13215 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052281552917 ∧
    0 ≤ bN 13215 BstLean.Part154.csC (groupTheta g) ∧ bN 13215 BstLean.Part154.csC (groupTheta g) ≤ 0.001324763850 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13215 13215 0.011
      (momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13215 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13215 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13215 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228651597233 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13215 0.011
      (momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13215 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13215
/-! The actual computed-centre upper energy formula at 13215. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13215

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13215)
open BstLean.Part268 (cell13215)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084114621117
  | 2 => 0.085036466266
  | 3 => 0.085953535028
  | 4 => 0.086866557466
  | 5 => 0.087776435663
  | 6 => 0.088684271558
  | 7 => 0.089591397842
  | 8 => 0.090499412032
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13215 13215 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13215 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13215

/-! Actual upper energy certificates on all 43 source endpoints at 13215. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13215)
open BstLean.Part268 (cell13215)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13215 (gMinus 13215) (1 - (cell13215 i).lower) ≤ 1 ∧
    energyUpper 13215 (gMinus 13215) (BstLean.Part211.gPlus 13215)
      (finiteEnergy 13215 13215 0.011) (1 - (cell13215 i).lower) ≤
      (cell13215 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨10,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨11,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨12,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨13,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨14,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨15,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨16,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨17,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨18,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨19,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨20,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨21,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨22,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨23,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨24,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨25,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨26,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨27,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨28,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨29,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨30,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨31,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨32,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨33,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨34,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨35,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨36,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨37,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨38,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨39,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨40,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨41,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨42,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨43,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨44,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨45,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨46,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨47,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨48,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨49,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨50,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨51,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13215) (by norm_num)
        (q := 1 - (cell13215 ⟨52,by decide⟩).lower)
        (by norm_num [cell13215]) (by norm_num [cell13215])
      exact ⟨E.1,E.2.trans (by norm_num [cell13215])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13215

/-! Source-cell containment and simple scalar guards at 13215. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13215)
open BstLean.Part268 (cell13215)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13215 ⟨10,by decide⟩).lower ∧ (cell13215 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13215 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13215 ⟨11,by decide⟩).lower ∧ (cell13215 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13215 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13215 ⟨12,by decide⟩).lower ∧ (cell13215 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13215 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13215 ⟨13,by decide⟩).lower ∧ (cell13215 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13215 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13215 ⟨14,by decide⟩).lower ∧ (cell13215 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13215 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13215 ⟨15,by decide⟩).lower ∧ (cell13215 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13215 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13215 ⟨16,by decide⟩).lower ∧ (cell13215 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13215 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13215 ⟨17,by decide⟩).lower ∧ (cell13215 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13215 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13215 ⟨18,by decide⟩).lower ∧ (cell13215 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13215 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13215 ⟨19,by decide⟩).lower ∧ (cell13215 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13215 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13215 ⟨20,by decide⟩).lower ∧ (cell13215 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13215 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13215 ⟨21,by decide⟩).lower ∧ (cell13215 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13215 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13215 ⟨22,by decide⟩).lower ∧ (cell13215 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13215 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13215 ⟨23,by decide⟩).lower ∧ (cell13215 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13215 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13215 ⟨24,by decide⟩).lower ∧ (cell13215 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13215 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13215 ⟨25,by decide⟩).lower ∧ (cell13215 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13215 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13215 ⟨26,by decide⟩).lower ∧ (cell13215 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13215 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13215 ⟨27,by decide⟩).lower ∧ (cell13215 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13215 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13215 ⟨28,by decide⟩).lower ∧ (cell13215 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13215 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13215 ⟨29,by decide⟩).lower ∧ (cell13215 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13215 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13215 ⟨30,by decide⟩).lower ∧ (cell13215 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13215 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13215 ⟨31,by decide⟩).lower ∧ (cell13215 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13215 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13215 ⟨32,by decide⟩).lower ∧ (cell13215 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13215 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13215 ⟨33,by decide⟩).lower ∧ (cell13215 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13215 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13215 ⟨34,by decide⟩).lower ∧ (cell13215 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13215 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13215 ⟨35,by decide⟩).lower ∧ (cell13215 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13215 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13215 ⟨36,by decide⟩).lower ∧ (cell13215 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13215 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13215 ⟨37,by decide⟩).lower ∧ (cell13215 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13215 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13215 ⟨38,by decide⟩).lower ∧ (cell13215 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13215 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13215 ⟨39,by decide⟩).lower ∧ (cell13215 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13215 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13215 ⟨40,by decide⟩).lower ∧ (cell13215 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13215 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13215 ⟨41,by decide⟩).lower ∧ (cell13215 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13215 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13215 ⟨42,by decide⟩).lower ∧ (cell13215 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13215 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13215 ⟨43,by decide⟩).lower ∧ (cell13215 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13215 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13215 ⟨44,by decide⟩).lower ∧ (cell13215 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13215 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13215 ⟨45,by decide⟩).lower ∧ (cell13215 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13215 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13215 ⟨46,by decide⟩).lower ∧ (cell13215 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13215 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13215 ⟨47,by decide⟩).lower ∧ (cell13215 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13215 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13215 ⟨48,by decide⟩).lower ∧ (cell13215 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13215 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13215 ⟨49,by decide⟩).lower ∧ (cell13215 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13215 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13215 ⟨50,by decide⟩).lower ∧ (cell13215 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13215 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13215 ⟨51,by decide⟩).lower ∧ (cell13215 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13215 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13215 ⟨52,by decide⟩).lower ∧ (cell13215 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13215 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13215 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13215 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13215,cell13215,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13215 i).lower ∧
    (cell13215 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13215 i).upper ≤ (0.532 : ℝ) ∧
    (cell13215 i).centre ≤ (0.1 : ℝ) ∧ (cell13215 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13215 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13215 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13215

/-! The local source numeric instances at 13215 have no network premises. -/
namespace BstLean.Part269.N13215
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13215)
open BstLean.Part268 (cell13215)

noncomputable def sourceNumerics13215 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13215 (cell13215 i)
      scalarRow13215.M scalarRow13215.H scalarRow13215.xi := by
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
    energy_allowance := scalarRow13215.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13215]
    centre_nonneg := (scalarRow13215.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13215])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13215
/-! Actual 13216 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13216 ≤ (1.035097113471 : ℝ) := by
  have hr : (114.960862905599 : ℝ) ≤ √(13216 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.960862905599 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13216 13216 (11 / 1000) ≤
    (0.008314889620 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13216) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.960862905599 : ℝ) ≤ √(13216 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13216)
  have hdiv : K / √(13216 : ℝ) ≤ K / 114.960862905599 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.960862905599 ≤ (0.008314889620 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13216.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13216 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13216 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13216 := gPlus_lower 13216
end BstLean.Part269.N13216

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13216
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035097113470 : ℝ) ≤ wn 13216 := by
  have hn : √(13216 : ℝ) ≤ 114.960862905600 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13216 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.960862905600 ≤ 2 / √(13216 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241880133 : ℝ) ≤ rhoBar 13216 BstLean.Part154.csC ∧
    rhoBar 13216 BstLean.Part154.csC ≤ 0.000241880507 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035097113470 : ℝ) / (1.295212 * 13216) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035097113471 : ℝ) / (1.29521 * 13216) := by gcongr
      _ ≤ (0.000241880507 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13216 BstLean.Part154.csC) ≤ 0.000967580535 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13216 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) ≤ 0.000184749622 ∧
    cc1 (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) ≤ 0.000117557481 ∧
    cc2 (rhoBar 13216 BstLean.Part154.csC) ≤ 0.000068243104 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13216 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13216 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13216 BstLean.Part154.csC * nuR (rhoBar 13216 BstLean.Part154.csC)) ≤ 0.000483775641 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241880507 : ℝ) * 0.000967580535 := by gcongr
      _ ≤ (0.000483775641 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13216 BstLean.Part154.csC) * nuR (rhoBar 13216 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967580535 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13216 BstLean.Part154.csC) * rhoBar 13216 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241880507 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241880507 / 2 + 0.399 * 0.000967580535 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184749622 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483775641 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117557481 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241880507 / 1.414213562 := by gcongr
      _ ≤ (0.000068243104 : ℝ) := by norm_num

end BstLean.Part269.N13216

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13216
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) ≤ 1.47402E-7 := by
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13216 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13216 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13216 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184749622 : ℝ) ^ 2 + 0.000117557481 ^ 2 + 3 * 0.000068243104 ^ 2 +
        2 * 0.797885 * 0.000184749622 * 0.000117557481 + 2 * 0.000184749622 * 0.000068243104 +
        4 * 0.797885 * 0.000117557481 * 0.000068243104 := by gcongr
    _ ≤ (1.47402E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13216 BstLean.Part154.csC Θ ≤ 0.002523156951 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13216 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13216 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13216 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035097113471 * 1.47402E-7 / (0.000241880133 : ℝ) := by gcongr
    _ ≤ 0.002523156951 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13216 BstLean.Part154.csC Θ ≤ 0.002797649662 + 0.000637561631 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13216 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13216 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035097113471 : ℝ) * ((2 * Θ * 0.000241880507 +
        (6863 / 10000) * 0.000241880507 * 13216 * 0.000967580535) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002797649662 + 0.000637561631 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13216 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13216 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13216 0.011 Θ ∧ gammaRatio 13216 0.011 Θ ≤ 0.000083152264 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13216 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035097113471 : ℝ) * 0.525 / ((1 - 0.011) * 13216) := by gcongr
      _ ≤ (0.000083152264 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13216 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13216 0.011 Θ) :=
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
    badAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13216 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13216 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13216 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13216 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13216 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13216 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13216 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13216 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13216 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13216 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035097113471 : ℝ) * 13216 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003115220428 + 0.003160718582 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13216

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13216
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13216 BstLean.Part154.csC) (piBar (rhoBar 13216 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13216 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13216 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13216 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13216 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13216 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13216 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13216 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13216 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13216 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13216 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051438524477 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13216) ≤ 0.010388209961 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13216 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035097113471)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010388209961 + 2 * 0.737676 / 13216) := by gcongr
    _ ≤ (0.051438524477 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13216 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13216

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13216
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525992259 : ℝ) ≤ plow 13216 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13216) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281197684)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324657400) : eMP 13216 0.011 xi bn ≤ 0.001141084294 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13216 : ℝ) * (1 - 0.011))) ≤ 0.000564259117 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324657400 / (13216 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564259117 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564259117 : ℝ) + 3.141593 * 0.052281197684 / (13216 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001141084294 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281197684)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324657400) : PiBarMP 13216 12 0.011 xi bn ≤ 0.158040990655 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13216 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036395843170 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.326829747002 : ℝ) ≤ √((13216 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.960862905599 : ℝ) ≤ √(13216 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13216) ≤ 0.121192620781 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036395843170 + 0.052281197684 * 1.772454 / (2 * (114.326829747002 : ℝ))) * (1 + 0.001141084294) +
        8 / (13216 * 114.960862905599) + 0.121192620781 := by gcongr
    _ ≤ (0.158040990655 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281197684)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324657400) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280089344909) :
    parallelOracle 13216 0.011 xi bn cd ≤ 0.158993181815 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13216 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13216 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525992259 : ℝ) ≤ plow 13216 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.960862905599 : ℝ) ≤ √(13216 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280089344909 : ℝ) / (2 * 0.560525992259 * 114.960862905599)) * 0.158040990655 +
        0.280089344909 ^ 2 / (2 * 0.560525992259 * 114.960862905599) := by gcongr
    _ ≤ (0.158993181815 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052281197684) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324657400)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280089344909) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13216 13216 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525992259 : ℝ) ≤ plow 13216 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.960862905599 : ℝ) ≤ √(13216 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13216 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13216 Θ 1.22 ≤ 0.011535234397 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.960862905599 := by gcongr <;> linarith
      _ ≤ (0.011535234397 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13216 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13216 13216 0.011 ≤ 0.008314889620 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13216 13216 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13216 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13216 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13216 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13216 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158993181815 + 0.011535234397 + (0.008314889620 : ℝ) *
        (1 + 2 * (0.280089344909 + 0.011535234397) / (0.560525992259 * 114.960862905599))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13216]

end BstLean.Part269.N13216

/-! The original eight local profiles supply actual 13216 moment certificates. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13216 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052281197684 ∧
    0 ≤ bN 13216 BstLean.Part154.csC (groupTheta g) ∧ bN 13216 BstLean.Part154.csC (groupTheta g) ≤ 0.001324657400 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13216 13216 0.011
      (momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13216 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13216 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13216 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228650820432 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13216 0.011
      (momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13216 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13216
/-! The actual computed-centre upper energy formula at 13216. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13216

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13216)
open BstLean.Part268 (cell13216)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084112160677
  | 2 => 0.085033976634
  | 3 => 0.085951012241
  | 4 => 0.086863996602
  | 5 => 0.087773830661
  | 6 => 0.088681615013
  | 7 => 0.089588680771
  | 8 => 0.090496623616
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13216 13216 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13216 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13216

/-! Actual upper energy certificates on all 43 source endpoints at 13216. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13216)
open BstLean.Part268 (cell13216)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13216 (gMinus 13216) (1 - (cell13216 i).lower) ≤ 1 ∧
    energyUpper 13216 (gMinus 13216) (BstLean.Part211.gPlus 13216)
      (finiteEnergy 13216 13216 0.011) (1 - (cell13216 i).lower) ≤
      (cell13216 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨10,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨11,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨12,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨13,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨14,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨15,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨16,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨17,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨18,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨19,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨20,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨21,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨22,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨23,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨24,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨25,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨26,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨27,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨28,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨29,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨30,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨31,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨32,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨33,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨34,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨35,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨36,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨37,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨38,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨39,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨40,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨41,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨42,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨43,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨44,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨45,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨46,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨47,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨48,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨49,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨50,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨51,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13216) (by norm_num)
        (q := 1 - (cell13216 ⟨52,by decide⟩).lower)
        (by norm_num [cell13216]) (by norm_num [cell13216])
      exact ⟨E.1,E.2.trans (by norm_num [cell13216])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13216

/-! Source-cell containment and simple scalar guards at 13216. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13216)
open BstLean.Part268 (cell13216)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13216 ⟨10,by decide⟩).lower ∧ (cell13216 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13216 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13216 ⟨11,by decide⟩).lower ∧ (cell13216 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13216 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13216 ⟨12,by decide⟩).lower ∧ (cell13216 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13216 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13216 ⟨13,by decide⟩).lower ∧ (cell13216 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13216 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13216 ⟨14,by decide⟩).lower ∧ (cell13216 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13216 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13216 ⟨15,by decide⟩).lower ∧ (cell13216 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13216 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13216 ⟨16,by decide⟩).lower ∧ (cell13216 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13216 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13216 ⟨17,by decide⟩).lower ∧ (cell13216 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13216 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13216 ⟨18,by decide⟩).lower ∧ (cell13216 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13216 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13216 ⟨19,by decide⟩).lower ∧ (cell13216 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13216 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13216 ⟨20,by decide⟩).lower ∧ (cell13216 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13216 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13216 ⟨21,by decide⟩).lower ∧ (cell13216 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13216 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13216 ⟨22,by decide⟩).lower ∧ (cell13216 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13216 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13216 ⟨23,by decide⟩).lower ∧ (cell13216 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13216 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13216 ⟨24,by decide⟩).lower ∧ (cell13216 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13216 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13216 ⟨25,by decide⟩).lower ∧ (cell13216 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13216 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13216 ⟨26,by decide⟩).lower ∧ (cell13216 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13216 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13216 ⟨27,by decide⟩).lower ∧ (cell13216 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13216 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13216 ⟨28,by decide⟩).lower ∧ (cell13216 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13216 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13216 ⟨29,by decide⟩).lower ∧ (cell13216 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13216 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13216 ⟨30,by decide⟩).lower ∧ (cell13216 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13216 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13216 ⟨31,by decide⟩).lower ∧ (cell13216 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13216 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13216 ⟨32,by decide⟩).lower ∧ (cell13216 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13216 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13216 ⟨33,by decide⟩).lower ∧ (cell13216 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13216 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13216 ⟨34,by decide⟩).lower ∧ (cell13216 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13216 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13216 ⟨35,by decide⟩).lower ∧ (cell13216 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13216 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13216 ⟨36,by decide⟩).lower ∧ (cell13216 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13216 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13216 ⟨37,by decide⟩).lower ∧ (cell13216 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13216 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13216 ⟨38,by decide⟩).lower ∧ (cell13216 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13216 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13216 ⟨39,by decide⟩).lower ∧ (cell13216 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13216 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13216 ⟨40,by decide⟩).lower ∧ (cell13216 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13216 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13216 ⟨41,by decide⟩).lower ∧ (cell13216 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13216 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13216 ⟨42,by decide⟩).lower ∧ (cell13216 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13216 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13216 ⟨43,by decide⟩).lower ∧ (cell13216 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13216 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13216 ⟨44,by decide⟩).lower ∧ (cell13216 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13216 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13216 ⟨45,by decide⟩).lower ∧ (cell13216 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13216 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13216 ⟨46,by decide⟩).lower ∧ (cell13216 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13216 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13216 ⟨47,by decide⟩).lower ∧ (cell13216 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13216 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13216 ⟨48,by decide⟩).lower ∧ (cell13216 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13216 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13216 ⟨49,by decide⟩).lower ∧ (cell13216 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13216 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13216 ⟨50,by decide⟩).lower ∧ (cell13216 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13216 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13216 ⟨51,by decide⟩).lower ∧ (cell13216 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13216 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13216 ⟨52,by decide⟩).lower ∧ (cell13216 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13216 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13216 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13216 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13216,cell13216,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13216 i).lower ∧
    (cell13216 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13216 i).upper ≤ (0.532 : ℝ) ∧
    (cell13216 i).centre ≤ (0.1 : ℝ) ∧ (cell13216 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13216 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13216 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13216

/-! The local source numeric instances at 13216 have no network premises. -/
namespace BstLean.Part269.N13216
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13216)
open BstLean.Part268 (cell13216)

noncomputable def sourceNumerics13216 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13216 (cell13216 i)
      scalarRow13216.M scalarRow13216.H scalarRow13216.xi := by
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
    energy_allowance := scalarRow13216.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13216]
    centre_nonneg := (scalarRow13216.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13216])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13216
/-! Actual 13217 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13217 ≤ (1.035095774270 : ℝ) := by
  have hr : (114.965212129582 : ℝ) ≤ √(13217 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.965212129582 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13217 13217 (11 / 1000) ≤
    (0.008314575059 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13217) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.965212129582 : ℝ) ≤ √(13217 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13217)
  have hdiv : K / √(13217 : ℝ) ≤ K / 114.965212129582 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.965212129582 ≤ (0.008314575059 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13217.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13217 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13217 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13217 := gPlus_lower 13217
end BstLean.Part269.N13217

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13217
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035095774269 : ℝ) ≤ wn 13217 := by
  have hn : √(13217 : ℝ) ≤ 114.965212129583 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13217 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.965212129583 ≤ 2 / √(13217 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241861519 : ℝ) ≤ rhoBar 13217 BstLean.Part154.csC ∧
    rhoBar 13217 BstLean.Part154.csC ≤ 0.000241861894 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035095774269 : ℝ) / (1.295212 * 13217) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035095774270 : ℝ) / (1.29521 * 13217) := by gcongr
      _ ≤ (0.000241861894 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13217 BstLean.Part154.csC) ≤ 0.000967506074 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13217 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) ≤ 0.000184735404 ∧
    cc1 (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) ≤ 0.000117548435 ∧
    cc2 (rhoBar 13217 BstLean.Part154.csC) ≤ 0.000068237852 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13217 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13217 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13217 BstLean.Part154.csC * nuR (rhoBar 13217 BstLean.Part154.csC)) ≤ 0.000483738413 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241861894 : ℝ) * 0.000967506074 := by gcongr
      _ ≤ (0.000483738413 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13217 BstLean.Part154.csC) * nuR (rhoBar 13217 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967506074 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13217 BstLean.Part154.csC) * rhoBar 13217 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241861894 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241861894 / 2 + 0.399 * 0.000967506074 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184735404 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483738413 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117548435 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241861894 / 1.414213562 := by gcongr
      _ ≤ (0.000068237852 : ℝ) := by norm_num

end BstLean.Part269.N13217

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13217
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) ≤ 1.47379E-7 := by
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13217 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13217 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13217 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184735404 : ℝ) ^ 2 + 0.000117548435 ^ 2 + 3 * 0.000068237852 ^ 2 +
        2 * 0.797885 * 0.000184735404 * 0.000117548435 + 2 * 0.000184735404 * 0.000068237852 +
        4 * 0.797885 * 0.000117548435 * 0.000068237852 := by gcongr
    _ ≤ (1.47379E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13217 BstLean.Part154.csC Θ ≤ 0.002522954140 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13217 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13217 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13217 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035095774270 * 1.47379E-7 / (0.000241861519 : ℝ) := by gcongr
    _ ≤ 0.002522954140 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13217 BstLean.Part154.csC Θ ≤ 0.002797427135 + 0.000637511745 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13217 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13217 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035095774270 : ℝ) * ((2 * Θ * 0.000241861894 +
        (6863 / 10000) * 0.000241861894 * 13217 * 0.000967506074) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002797427135 + 0.000637511745 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13217 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13217 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13217 0.011 Θ ∧ gammaRatio 13217 0.011 Θ ≤ 0.000083145865 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13217 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035095774270 : ℝ) * 0.525 / ((1 - 0.011) * 13217) := by gcongr
      _ ≤ (0.000083145865 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13217 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13217 0.011 Θ) :=
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
    badAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13217 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13217 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13217 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13217 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13217 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13217 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13217 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13217 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13217 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13217 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035095774270 : ℝ) * 13217 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003114997901 + 0.003160465885 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13217

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13217
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13217 BstLean.Part154.csC) (piBar (rhoBar 13217 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13217 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13217 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13217 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13217 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13217 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13217 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13217 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13217 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13217 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13217 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051436557825 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13217) ≤ 0.010387816966 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13217 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035095774270)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010387816966 + 2 * 0.737676 / 13217) := by gcongr
    _ ≤ (0.051436557825 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13217 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13217

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13217
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526034016 : ℝ) ≤ plow 13217 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13217) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280842491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324550924) : eMP 13217 0.011 xi bn ≤ 0.001140995210 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13217 : ℝ) * (1 - 0.011))) ≤ 0.000564215093 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324550924 / (13217 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564215093 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564215093 : ℝ) + 3.141593 * 0.052280842491 / (13217 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140995210 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280842491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324550924) : PiBarMP 13217 12 0.011 xi bn ≤ 0.158034919414 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13217 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036394380391 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.331154984107 : ℝ) ≤ √((13217 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.965212129582 : ℝ) ≤ √(13217 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13217) ≤ 0.121188035970 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036394380391 + 0.052280842491 * 1.772454 / (2 * (114.331154984107 : ℝ))) * (1 + 0.001140995210) +
        8 / (13217 * 114.965212129582) + 0.121188035970 := by gcongr
    _ ≤ (0.158034919414 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280842491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324550924) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280086601541) :
    parallelOracle 13217 0.011 xi bn cd ≤ 0.158987045999 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13217 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13217 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526034016 : ℝ) ≤ plow 13217 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.965212129582 : ℝ) ≤ √(13217 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280086601541 : ℝ) / (2 * 0.560526034016 * 114.965212129582)) * 0.158034919414 +
        0.280086601541 ^ 2 / (2 * 0.560526034016 * 114.965212129582) := by gcongr
    _ ≤ (0.158987045999 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280842491) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324550924)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280086601541) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13217 13217 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526034016 : ℝ) ≤ plow 13217 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.965212129582 : ℝ) ≤ √(13217 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13217 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13217 Θ 1.22 ≤ 0.011534798010 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.965212129582 := by gcongr <;> linarith
      _ ≤ (0.011534798010 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13217 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13217 13217 0.011 ≤ 0.008314575059 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13217 13217 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13217 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13217 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13217 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13217 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158987045999 + 0.011534798010 + (0.008314575059 : ℝ) *
        (1 + 2 * (0.280086601541 + 0.011534798010) / (0.560526034016 * 114.965212129582))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13217]

end BstLean.Part269.N13217

/-! The original eight local profiles supply actual 13217 moment certificates. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13217 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052280842491 ∧
    0 ≤ bN 13217 BstLean.Part154.csC (groupTheta g) ∧ bN 13217 BstLean.Part154.csC (groupTheta g) ≤ 0.001324550924 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13217 13217 0.011
      (momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13217 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13217 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13217 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228650043716 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13217 0.011
      (momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13217 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13217
/-! The actual computed-centre upper energy formula at 13217. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13217

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13217)
open BstLean.Part268 (cell13217)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084109700902
  | 2 => 0.085031487689
  | 3 => 0.085948490168
  | 4 => 0.086861436486
  | 5 => 0.087771226449
  | 6 => 0.088678959308
  | 7 => 0.089585964600
  | 8 => 0.090493836173
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13217 13217 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13217 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13217

/-! Actual upper energy certificates on all 43 source endpoints at 13217. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13217)
open BstLean.Part268 (cell13217)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13217 (gMinus 13217) (1 - (cell13217 i).lower) ≤ 1 ∧
    energyUpper 13217 (gMinus 13217) (BstLean.Part211.gPlus 13217)
      (finiteEnergy 13217 13217 0.011) (1 - (cell13217 i).lower) ≤
      (cell13217 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨10,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨11,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨12,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨13,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨14,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨15,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨16,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨17,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨18,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨19,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨20,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨21,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨22,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨23,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨24,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨25,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨26,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨27,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨28,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨29,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨30,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨31,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨32,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨33,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨34,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨35,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨36,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨37,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨38,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨39,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨40,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨41,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨42,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨43,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨44,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨45,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨46,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨47,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨48,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨49,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨50,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨51,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13217) (by norm_num)
        (q := 1 - (cell13217 ⟨52,by decide⟩).lower)
        (by norm_num [cell13217]) (by norm_num [cell13217])
      exact ⟨E.1,E.2.trans (by norm_num [cell13217])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13217

/-! Source-cell containment and simple scalar guards at 13217. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13217)
open BstLean.Part268 (cell13217)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13217 ⟨10,by decide⟩).lower ∧ (cell13217 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13217 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13217 ⟨11,by decide⟩).lower ∧ (cell13217 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13217 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13217 ⟨12,by decide⟩).lower ∧ (cell13217 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13217 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13217 ⟨13,by decide⟩).lower ∧ (cell13217 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13217 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13217 ⟨14,by decide⟩).lower ∧ (cell13217 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13217 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13217 ⟨15,by decide⟩).lower ∧ (cell13217 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13217 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13217 ⟨16,by decide⟩).lower ∧ (cell13217 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13217 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13217 ⟨17,by decide⟩).lower ∧ (cell13217 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13217 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13217 ⟨18,by decide⟩).lower ∧ (cell13217 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13217 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13217 ⟨19,by decide⟩).lower ∧ (cell13217 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13217 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13217 ⟨20,by decide⟩).lower ∧ (cell13217 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13217 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13217 ⟨21,by decide⟩).lower ∧ (cell13217 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13217 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13217 ⟨22,by decide⟩).lower ∧ (cell13217 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13217 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13217 ⟨23,by decide⟩).lower ∧ (cell13217 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13217 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13217 ⟨24,by decide⟩).lower ∧ (cell13217 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13217 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13217 ⟨25,by decide⟩).lower ∧ (cell13217 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13217 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13217 ⟨26,by decide⟩).lower ∧ (cell13217 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13217 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13217 ⟨27,by decide⟩).lower ∧ (cell13217 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13217 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13217 ⟨28,by decide⟩).lower ∧ (cell13217 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13217 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13217 ⟨29,by decide⟩).lower ∧ (cell13217 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13217 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13217 ⟨30,by decide⟩).lower ∧ (cell13217 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13217 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13217 ⟨31,by decide⟩).lower ∧ (cell13217 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13217 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13217 ⟨32,by decide⟩).lower ∧ (cell13217 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13217 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13217 ⟨33,by decide⟩).lower ∧ (cell13217 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13217 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13217 ⟨34,by decide⟩).lower ∧ (cell13217 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13217 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13217 ⟨35,by decide⟩).lower ∧ (cell13217 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13217 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13217 ⟨36,by decide⟩).lower ∧ (cell13217 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13217 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13217 ⟨37,by decide⟩).lower ∧ (cell13217 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13217 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13217 ⟨38,by decide⟩).lower ∧ (cell13217 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13217 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13217 ⟨39,by decide⟩).lower ∧ (cell13217 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13217 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13217 ⟨40,by decide⟩).lower ∧ (cell13217 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13217 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13217 ⟨41,by decide⟩).lower ∧ (cell13217 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13217 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13217 ⟨42,by decide⟩).lower ∧ (cell13217 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13217 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13217 ⟨43,by decide⟩).lower ∧ (cell13217 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13217 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13217 ⟨44,by decide⟩).lower ∧ (cell13217 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13217 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13217 ⟨45,by decide⟩).lower ∧ (cell13217 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13217 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13217 ⟨46,by decide⟩).lower ∧ (cell13217 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13217 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13217 ⟨47,by decide⟩).lower ∧ (cell13217 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13217 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13217 ⟨48,by decide⟩).lower ∧ (cell13217 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13217 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13217 ⟨49,by decide⟩).lower ∧ (cell13217 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13217 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13217 ⟨50,by decide⟩).lower ∧ (cell13217 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13217 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13217 ⟨51,by decide⟩).lower ∧ (cell13217 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13217 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13217 ⟨52,by decide⟩).lower ∧ (cell13217 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13217 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13217 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13217 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13217,cell13217,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13217 i).lower ∧
    (cell13217 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13217 i).upper ≤ (0.532 : ℝ) ∧
    (cell13217 i).centre ≤ (0.1 : ℝ) ∧ (cell13217 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13217 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13217 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13217

/-! The local source numeric instances at 13217 have no network premises. -/
namespace BstLean.Part269.N13217
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13217)
open BstLean.Part268 (cell13217)

noncomputable def sourceNumerics13217 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13217 (cell13217 i)
      scalarRow13217.M scalarRow13217.H scalarRow13217.xi := by
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
    energy_allowance := scalarRow13217.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13217]
    centre_nonneg := (scalarRow13217.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13217])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13217
/-! Actual 13218 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13218 ≤ (1.035094435222 : ℝ) := by
  have hr : (114.969561189038 : ℝ) ≤ √(13218 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.969561189038 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13218 13218 (11 / 1000) ≤
    (0.008314260533 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13218) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.969561189038 : ℝ) ≤ √(13218 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13218)
  have hdiv : K / √(13218 : ℝ) ≤ K / 114.969561189038 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.969561189038 ≤ (0.008314260533 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13218.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13218 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13218 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13218 := gPlus_lower 13218
end BstLean.Part269.N13218

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13218
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035094435221 : ℝ) ≤ wn 13218 := by
  have hn : √(13218 : ℝ) ≤ 114.969561189039 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13218 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.969561189039 ≤ 2 / √(13218 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241842909 : ℝ) ≤ rhoBar 13218 BstLean.Part154.csC ∧
    rhoBar 13218 BstLean.Part154.csC ≤ 0.000241843283 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035094435221 : ℝ) / (1.295212 * 13218) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035094435222 : ℝ) / (1.29521 * 13218) := by gcongr
      _ ≤ (0.000241843283 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13218 BstLean.Part154.csC) ≤ 0.000967431621 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13218 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) ≤ 0.000184721189 ∧
    cc1 (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) ≤ 0.000117539389 ∧
    cc2 (rhoBar 13218 BstLean.Part154.csC) ≤ 0.000068232602 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13218 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13218 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13218 BstLean.Part154.csC * nuR (rhoBar 13218 BstLean.Part154.csC)) ≤ 0.000483701189 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241843283 : ℝ) * 0.000967431621 := by gcongr
      _ ≤ (0.000483701189 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13218 BstLean.Part154.csC) * nuR (rhoBar 13218 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967431621 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13218 BstLean.Part154.csC) * rhoBar 13218 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241843283 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241843283 / 2 + 0.399 * 0.000967431621 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184721189 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483701189 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117539389 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241843283 / 1.414213562 := by gcongr
      _ ≤ (0.000068232602 : ℝ) := by norm_num

end BstLean.Part269.N13218

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13218
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) ≤ 1.47357E-7 := by
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13218 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13218 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13218 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184721189 : ℝ) ^ 2 + 0.000117539389 ^ 2 + 3 * 0.000068232602 ^ 2 +
        2 * 0.797885 * 0.000184721189 * 0.000117539389 + 2 * 0.000184721189 * 0.000068232602 +
        4 * 0.797885 * 0.000117539389 * 0.000068232602 := by gcongr
    _ ≤ (1.47357E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13218 BstLean.Part154.csC Θ ≤ 0.002522768376 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13218 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13218 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13218 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035094435222 * 1.47357E-7 / (0.000241842909 : ℝ) := by gcongr
    _ ≤ 0.002522768376 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13218 BstLean.Part154.csC Θ ≤ 0.002797204623 + 0.000637461864 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13218 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13218 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035094435222 : ℝ) * ((2 * Θ * 0.000241843283 +
        (6863 / 10000) * 0.000241843283 * 13218 * 0.000967431621) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002797204623 + 0.000637461864 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13218 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13218 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13218 0.011 Θ ∧ gammaRatio 13218 0.011 Θ ≤ 0.000083139467 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13218 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035094435222 : ℝ) * 0.525 / ((1 - 0.011) * 13218) := by gcongr
      _ ≤ (0.000083139467 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13218 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13218 0.011 Θ) :=
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
    badAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13218 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13218 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13218 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13218 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13218 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13218 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13218 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13218 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13218 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13218 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035094435222 : ℝ) * 13218 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003114775389 + 0.003160230240 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13218

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13218
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13218 BstLean.Part154.csC) (piBar (rhoBar 13218 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13218 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13218 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13218 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13218 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13218 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13218 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13218 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13218 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13218 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13218 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051434591404 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13218) ≤ 0.010387424017 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13218 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035094435222)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010387424017 + 2 * 0.737676 / 13218) := by gcongr
    _ ≤ (0.051434591404 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13218 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13218

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13218
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526075767 : ℝ) ≤ plow 13218 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13218) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280496265)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324453398) : eMP 13218 0.011 xi bn ≤ 0.001140909949 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13218 : ℝ) * (1 - 0.011))) ≤ 0.000564172979 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324453398 / (13218 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564172979 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564172979 : ℝ) + 3.141593 * 0.052280496265 / (13218 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140909949 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280496265)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324453398) : PiBarMP 13218 12 0.011 xi bn ≤ 0.158028971951 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13218 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036393040517 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.335480057591 : ℝ) ≤ √((13218 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.969561189038 : ℝ) ≤ √(13218 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13218) ≤ 0.121183451678 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036393040517 + 0.052280496265 * 1.772454 / (2 * (114.335480057591 : ℝ))) * (1 + 0.001140909949) +
        8 / (13218 * 114.969561189038) + 0.121183451678 := by gcongr
    _ ≤ (0.158028971951 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280496265)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324453398) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280083878010) :
    parallelOracle 13218 0.011 xi bn cd ≤ 0.158981034348 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13218 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13218 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526075767 : ℝ) ≤ plow 13218 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.969561189038 : ℝ) ≤ √(13218 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280083878010 : ℝ) / (2 * 0.560526075767 * 114.969561189038)) * 0.158028971951 +
        0.280083878010 ^ 2 / (2 * 0.560526075767 * 114.969561189038) := by gcongr
    _ ≤ (0.158981034348 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280496265) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324453398)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280083878010) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13218 13218 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526075767 : ℝ) ≤ plow 13218 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.969561189038 : ℝ) ≤ √(13218 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13218 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13218 Θ 1.22 ≤ 0.011534361672 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.969561189038 := by gcongr <;> linarith
      _ ≤ (0.011534361672 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13218 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13218 13218 0.011 ≤ 0.008314260533 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13218 13218 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13218 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13218 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13218 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13218 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158981034348 + 0.011534361672 + (0.008314260533 : ℝ) *
        (1 + 2 * (0.280083878010 + 0.011534361672) / (0.560526075767 * 114.969561189038))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13218]

end BstLean.Part269.N13218

/-! The original eight local profiles supply actual 13218 moment certificates. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13218 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052280496265 ∧
    0 ≤ bN 13218 BstLean.Part154.csC (groupTheta g) ∧ bN 13218 BstLean.Part154.csC (groupTheta g) ≤ 0.001324453398 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13218 13218 0.011
      (momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13218 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13218 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13218 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228649286606 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13218 0.011
      (momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13218 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13218
/-! The actual computed-centre upper energy formula at 13218. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13218

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13218)
open BstLean.Part268 (cell13218)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084107241794
  | 2 => 0.085028999432
  | 3 => 0.085945968810
  | 4 => 0.086858877117
  | 5 => 0.087768623024
  | 6 => 0.088676304440
  | 7 => 0.089583249329
  | 8 => 0.090491049703
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13218 13218 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13218 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13218

/-! Actual upper energy certificates on all 43 source endpoints at 13218. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13218)
open BstLean.Part268 (cell13218)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13218 (gMinus 13218) (1 - (cell13218 i).lower) ≤ 1 ∧
    energyUpper 13218 (gMinus 13218) (BstLean.Part211.gPlus 13218)
      (finiteEnergy 13218 13218 0.011) (1 - (cell13218 i).lower) ≤
      (cell13218 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨10,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨11,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨12,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨13,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨14,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨15,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨16,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨17,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨18,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨19,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨20,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨21,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨22,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨23,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨24,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨25,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨26,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨27,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨28,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨29,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨30,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨31,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨32,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨33,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨34,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨35,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨36,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨37,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨38,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨39,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨40,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨41,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨42,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨43,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨44,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨45,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨46,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨47,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨48,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨49,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨50,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨51,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13218) (by norm_num)
        (q := 1 - (cell13218 ⟨52,by decide⟩).lower)
        (by norm_num [cell13218]) (by norm_num [cell13218])
      exact ⟨E.1,E.2.trans (by norm_num [cell13218])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13218

/-! Source-cell containment and simple scalar guards at 13218. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13218)
open BstLean.Part268 (cell13218)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13218 ⟨10,by decide⟩).lower ∧ (cell13218 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13218 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13218 ⟨11,by decide⟩).lower ∧ (cell13218 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13218 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13218 ⟨12,by decide⟩).lower ∧ (cell13218 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13218 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13218 ⟨13,by decide⟩).lower ∧ (cell13218 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13218 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13218 ⟨14,by decide⟩).lower ∧ (cell13218 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13218 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13218 ⟨15,by decide⟩).lower ∧ (cell13218 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13218 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13218 ⟨16,by decide⟩).lower ∧ (cell13218 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13218 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13218 ⟨17,by decide⟩).lower ∧ (cell13218 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13218 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13218 ⟨18,by decide⟩).lower ∧ (cell13218 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13218 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13218 ⟨19,by decide⟩).lower ∧ (cell13218 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13218 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13218 ⟨20,by decide⟩).lower ∧ (cell13218 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13218 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13218 ⟨21,by decide⟩).lower ∧ (cell13218 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13218 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13218 ⟨22,by decide⟩).lower ∧ (cell13218 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13218 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13218 ⟨23,by decide⟩).lower ∧ (cell13218 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13218 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13218 ⟨24,by decide⟩).lower ∧ (cell13218 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13218 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13218 ⟨25,by decide⟩).lower ∧ (cell13218 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13218 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13218 ⟨26,by decide⟩).lower ∧ (cell13218 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13218 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13218 ⟨27,by decide⟩).lower ∧ (cell13218 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13218 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13218 ⟨28,by decide⟩).lower ∧ (cell13218 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13218 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13218 ⟨29,by decide⟩).lower ∧ (cell13218 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13218 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13218 ⟨30,by decide⟩).lower ∧ (cell13218 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13218 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13218 ⟨31,by decide⟩).lower ∧ (cell13218 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13218 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13218 ⟨32,by decide⟩).lower ∧ (cell13218 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13218 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13218 ⟨33,by decide⟩).lower ∧ (cell13218 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13218 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13218 ⟨34,by decide⟩).lower ∧ (cell13218 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13218 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13218 ⟨35,by decide⟩).lower ∧ (cell13218 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13218 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13218 ⟨36,by decide⟩).lower ∧ (cell13218 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13218 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13218 ⟨37,by decide⟩).lower ∧ (cell13218 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13218 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13218 ⟨38,by decide⟩).lower ∧ (cell13218 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13218 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13218 ⟨39,by decide⟩).lower ∧ (cell13218 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13218 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13218 ⟨40,by decide⟩).lower ∧ (cell13218 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13218 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13218 ⟨41,by decide⟩).lower ∧ (cell13218 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13218 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13218 ⟨42,by decide⟩).lower ∧ (cell13218 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13218 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13218 ⟨43,by decide⟩).lower ∧ (cell13218 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13218 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13218 ⟨44,by decide⟩).lower ∧ (cell13218 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13218 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13218 ⟨45,by decide⟩).lower ∧ (cell13218 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13218 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13218 ⟨46,by decide⟩).lower ∧ (cell13218 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13218 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13218 ⟨47,by decide⟩).lower ∧ (cell13218 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13218 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13218 ⟨48,by decide⟩).lower ∧ (cell13218 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13218 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13218 ⟨49,by decide⟩).lower ∧ (cell13218 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13218 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13218 ⟨50,by decide⟩).lower ∧ (cell13218 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13218 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13218 ⟨51,by decide⟩).lower ∧ (cell13218 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13218 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13218 ⟨52,by decide⟩).lower ∧ (cell13218 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13218 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13218 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13218 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13218,cell13218,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13218 i).lower ∧
    (cell13218 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13218 i).upper ≤ (0.532 : ℝ) ∧
    (cell13218 i).centre ≤ (0.1 : ℝ) ∧ (cell13218 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13218 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13218 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13218

/-! The local source numeric instances at 13218 have no network premises. -/
namespace BstLean.Part269.N13218
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13218)
open BstLean.Part268 (cell13218)

noncomputable def sourceNumerics13218 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13218 (cell13218 i)
      scalarRow13218.M scalarRow13218.H scalarRow13218.xi := by
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
    energy_allowance := scalarRow13218.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13218]
    centre_nonneg := (scalarRow13218.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13218])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13218
/-! Actual 13219 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13219 ≤ (1.035093096327 : ℝ) := by
  have hr : (114.973910083983 : ℝ) ≤ √(13219 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.973910083983 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13219 13219 (11 / 1000) ≤
    (0.008313946043 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13219) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.973910083983 : ℝ) ≤ √(13219 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13219)
  have hdiv : K / √(13219 : ℝ) ≤ K / 114.973910083983 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.973910083983 ≤ (0.008313946043 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13219.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13219 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13219 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13219 := gPlus_lower 13219
end BstLean.Part269.N13219

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13219
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035093096326 : ℝ) ≤ wn 13219 := by
  have hn : √(13219 : ℝ) ≤ 114.973910083984 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13219 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.973910083984 ≤ 2 / √(13219 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241824301 : ℝ) ≤ rhoBar 13219 BstLean.Part154.csC ∧
    rhoBar 13219 BstLean.Part154.csC ≤ 0.000241824675 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035093096326 : ℝ) / (1.295212 * 13219) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035093096327 : ℝ) / (1.29521 * 13219) := by gcongr
      _ ≤ (0.000241824675 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13219 BstLean.Part154.csC) ≤ 0.000967357180 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13219 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) ≤ 0.000184706975 ∧
    cc1 (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) ≤ 0.000117530345 ∧
    cc2 (rhoBar 13219 BstLean.Part154.csC) ≤ 0.000068227352 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13219 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13219 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13219 BstLean.Part154.csC * nuR (rhoBar 13219 BstLean.Part154.csC)) ≤ 0.000483663970 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241824675 : ℝ) * 0.000967357180 := by gcongr
      _ ≤ (0.000483663970 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13219 BstLean.Part154.csC) * nuR (rhoBar 13219 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967357180 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13219 BstLean.Part154.csC) * rhoBar 13219 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241824675 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241824675 / 2 + 0.399 * 0.000967357180 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184706975 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483663970 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117530345 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241824675 / 1.414213562 := by gcongr
      _ ≤ (0.000068227352 : ℝ) := by norm_num

end BstLean.Part269.N13219

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13219
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) ≤ 1.47334E-7 := by
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13219 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13219 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13219 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184706975 : ℝ) ^ 2 + 0.000117530345 ^ 2 + 3 * 0.000068227352 ^ 2 +
        2 * 0.797885 * 0.000184706975 * 0.000117530345 + 2 * 0.000184706975 * 0.000068227352 +
        4 * 0.797885 * 0.000117530345 * 0.000068227352 := by gcongr
    _ ≤ (1.47334E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13219 BstLean.Part154.csC Θ ≤ 0.002522565444 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13219 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13219 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13219 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035093096327 * 1.47334E-7 / (0.000241824301 : ℝ) := by gcongr
    _ ≤ 0.002522565444 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13219 BstLean.Part154.csC Θ ≤ 0.002796982150 + 0.000637411992 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13219 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13219 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035093096327 : ℝ) * ((2 * Θ * 0.000241824675 +
        (6863 / 10000) * 0.000241824675 * 13219 * 0.000967357180) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002796982150 + 0.000637411992 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13219 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13219 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13219 0.011 Θ ∧ gammaRatio 13219 0.011 Θ ≤ 0.000083133070 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13219 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035093096327 : ℝ) * 0.525 / ((1 - 0.011) * 13219) := by gcongr
      _ ≤ (0.000083133070 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13219 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13219 0.011 Θ) :=
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
    badAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13219 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13219 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13219 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13219 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13219 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13219 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13219 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13219 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13219 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13219 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035093096327 : ℝ) * 13219 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003114552916 + 0.003159977436 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13219

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13219
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13219 BstLean.Part154.csC) (piBar (rhoBar 13219 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13219 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13219 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13219 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13219 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13219 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13219 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13219 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13219 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13219 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13219 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051432625205 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13219) ≤ 0.010387031112 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13219 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035093096327)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010387031112 + 2 * 0.737676 / 13219) := by gcongr
    _ ≤ (0.051432625205 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13219 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13219

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13219
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526117512 : ℝ) ≤ plow 13219 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13219) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280141070)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324346859) : eMP 13219 0.011 xi bn ≤ 0.001140820853 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13219 : ℝ) * (1 - 0.011))) ≤ 0.000564128949 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324346859 / (13219 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564128949 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564128949 : ℝ) + 3.141593 * 0.052280141070 / (13219 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140820853 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280141070)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324346859) : PiBarMP 13219 12 0.011 xi bn ≤ 0.158022900774 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13219 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036391576759 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.339804967474 : ℝ) ≤ √((13219 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.973910083983 : ℝ) ≤ √(13219 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13219) ≤ 0.121178867907 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036391576759 + 0.052280141070 * 1.772454 / (2 * (114.339804967474 : ℝ))) * (1 + 0.001140820853) +
        8 / (13219 * 114.973910083983) + 0.121178867907 := by gcongr
    _ ≤ (0.158022900774 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280141070)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324346859) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280081135085) :
    parallelOracle 13219 0.011 xi bn cd ≤ 0.158974898611 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13219 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13219 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526117512 : ℝ) ≤ plow 13219 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.973910083983 : ℝ) ≤ √(13219 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280081135085 : ℝ) / (2 * 0.560526117512 * 114.973910083983)) * 0.158022900774 +
        0.280081135085 ^ 2 / (2 * 0.560526117512 * 114.973910083983) := by gcongr
    _ ≤ (0.158974898611 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052280141070) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324346859)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280081135085) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13219 13219 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526117512 : ℝ) ≤ plow 13219 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.973910083983 : ℝ) ≤ √(13219 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13219 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13219 Θ 1.22 ≤ 0.011533925384 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.973910083983 := by gcongr <;> linarith
      _ ≤ (0.011533925384 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13219 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13219 13219 0.011 ≤ 0.008313946043 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13219 13219 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13219 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13219 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13219 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13219 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158974898611 + 0.011533925384 + (0.008313946043 : ℝ) *
        (1 + 2 * (0.280081135085 + 0.011533925384) / (0.560526117512 * 114.973910083983))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13219]

end BstLean.Part269.N13219

/-! The original eight local profiles supply actual 13219 moment certificates. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13219 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052280141070 ∧
    0 ≤ bN 13219 BstLean.Part154.csC (groupTheta g) ∧ bN 13219 BstLean.Part154.csC (groupTheta g) ≤ 0.001324346859 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13219 13219 0.011
      (momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13219 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13219 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13219 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228648509880 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13219 0.011
      (momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13219 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13219
/-! The actual computed-centre upper energy formula at 13219. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13219

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13219)
open BstLean.Part268 (cell13219)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084104783351
  | 2 => 0.085026511862
  | 3 => 0.085943448165
  | 4 => 0.086856318495
  | 5 => 0.087766020387
  | 6 => 0.088673650409
  | 7 => 0.089580534955
  | 8 => 0.090488264204
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13219 13219 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13219 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13219

/-! Actual upper energy certificates on all 43 source endpoints at 13219. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13219)
open BstLean.Part268 (cell13219)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13219 (gMinus 13219) (1 - (cell13219 i).lower) ≤ 1 ∧
    energyUpper 13219 (gMinus 13219) (BstLean.Part211.gPlus 13219)
      (finiteEnergy 13219 13219 0.011) (1 - (cell13219 i).lower) ≤
      (cell13219 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨10,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨11,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨12,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨13,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨14,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨15,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨16,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨17,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨18,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨19,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨20,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨21,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨22,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨23,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨24,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨25,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨26,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨27,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨28,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨29,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨30,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨31,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨32,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨33,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨34,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨35,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨36,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨37,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨38,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨39,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨40,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨41,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨42,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨43,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨44,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨45,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨46,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨47,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨48,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨49,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨50,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨51,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13219) (by norm_num)
        (q := 1 - (cell13219 ⟨52,by decide⟩).lower)
        (by norm_num [cell13219]) (by norm_num [cell13219])
      exact ⟨E.1,E.2.trans (by norm_num [cell13219])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13219

/-! Source-cell containment and simple scalar guards at 13219. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13219)
open BstLean.Part268 (cell13219)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13219 ⟨10,by decide⟩).lower ∧ (cell13219 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13219 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13219 ⟨11,by decide⟩).lower ∧ (cell13219 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13219 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13219 ⟨12,by decide⟩).lower ∧ (cell13219 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13219 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13219 ⟨13,by decide⟩).lower ∧ (cell13219 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13219 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13219 ⟨14,by decide⟩).lower ∧ (cell13219 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13219 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13219 ⟨15,by decide⟩).lower ∧ (cell13219 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13219 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13219 ⟨16,by decide⟩).lower ∧ (cell13219 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13219 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13219 ⟨17,by decide⟩).lower ∧ (cell13219 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13219 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13219 ⟨18,by decide⟩).lower ∧ (cell13219 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13219 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13219 ⟨19,by decide⟩).lower ∧ (cell13219 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13219 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13219 ⟨20,by decide⟩).lower ∧ (cell13219 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13219 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13219 ⟨21,by decide⟩).lower ∧ (cell13219 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13219 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13219 ⟨22,by decide⟩).lower ∧ (cell13219 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13219 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13219 ⟨23,by decide⟩).lower ∧ (cell13219 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13219 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13219 ⟨24,by decide⟩).lower ∧ (cell13219 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13219 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13219 ⟨25,by decide⟩).lower ∧ (cell13219 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13219 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13219 ⟨26,by decide⟩).lower ∧ (cell13219 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13219 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13219 ⟨27,by decide⟩).lower ∧ (cell13219 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13219 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13219 ⟨28,by decide⟩).lower ∧ (cell13219 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13219 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13219 ⟨29,by decide⟩).lower ∧ (cell13219 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13219 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13219 ⟨30,by decide⟩).lower ∧ (cell13219 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13219 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13219 ⟨31,by decide⟩).lower ∧ (cell13219 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13219 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13219 ⟨32,by decide⟩).lower ∧ (cell13219 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13219 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13219 ⟨33,by decide⟩).lower ∧ (cell13219 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13219 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13219 ⟨34,by decide⟩).lower ∧ (cell13219 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13219 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13219 ⟨35,by decide⟩).lower ∧ (cell13219 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13219 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13219 ⟨36,by decide⟩).lower ∧ (cell13219 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13219 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13219 ⟨37,by decide⟩).lower ∧ (cell13219 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13219 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13219 ⟨38,by decide⟩).lower ∧ (cell13219 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13219 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13219 ⟨39,by decide⟩).lower ∧ (cell13219 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13219 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13219 ⟨40,by decide⟩).lower ∧ (cell13219 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13219 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13219 ⟨41,by decide⟩).lower ∧ (cell13219 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13219 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13219 ⟨42,by decide⟩).lower ∧ (cell13219 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13219 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13219 ⟨43,by decide⟩).lower ∧ (cell13219 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13219 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13219 ⟨44,by decide⟩).lower ∧ (cell13219 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13219 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13219 ⟨45,by decide⟩).lower ∧ (cell13219 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13219 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13219 ⟨46,by decide⟩).lower ∧ (cell13219 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13219 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13219 ⟨47,by decide⟩).lower ∧ (cell13219 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13219 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13219 ⟨48,by decide⟩).lower ∧ (cell13219 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13219 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13219 ⟨49,by decide⟩).lower ∧ (cell13219 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13219 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13219 ⟨50,by decide⟩).lower ∧ (cell13219 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13219 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13219 ⟨51,by decide⟩).lower ∧ (cell13219 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13219 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13219 ⟨52,by decide⟩).lower ∧ (cell13219 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13219 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13219 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13219 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13219,cell13219,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13219 i).lower ∧
    (cell13219 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13219 i).upper ≤ (0.532 : ℝ) ∧
    (cell13219 i).centre ≤ (0.1 : ℝ) ∧ (cell13219 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13219 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13219 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13219

/-! The local source numeric instances at 13219 have no network premises. -/
namespace BstLean.Part269.N13219
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13219)
open BstLean.Part268 (cell13219)

noncomputable def sourceNumerics13219 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13219 (cell13219 i)
      scalarRow13219.M scalarRow13219.H scalarRow13219.xi := by
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
    energy_allowance := scalarRow13219.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13219]
    centre_nonneg := (scalarRow13219.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13219])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13219
/-! Actual 13220 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13220 ≤ (1.035091757584 : ℝ) := by
  have hr : (114.978258814438 : ℝ) ≤ √(13220 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.978258814438 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13220 13220 (11 / 1000) ≤
    (0.008313631589 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13220) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.978258814438 : ℝ) ≤ √(13220 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13220)
  have hdiv : K / √(13220 : ℝ) ≤ K / 114.978258814438 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.978258814438 ≤ (0.008313631589 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13220.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13220 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13220 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13220 := gPlus_lower 13220
end BstLean.Part269.N13220

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13220
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035091757583 : ℝ) ≤ wn 13220 := by
  have hn : √(13220 : ℝ) ≤ 114.978258814439 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13220 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.978258814439 ≤ 2 / √(13220 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241805696 : ℝ) ≤ rhoBar 13220 BstLean.Part154.csC ∧
    rhoBar 13220 BstLean.Part154.csC ≤ 0.000241806070 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035091757583 : ℝ) / (1.295212 * 13220) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035091757584 : ℝ) / (1.29521 * 13220) := by gcongr
      _ ≤ (0.000241806070 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13220 BstLean.Part154.csC) ≤ 0.000967282751 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13220 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) ≤ 0.000184692764 ∧
    cc1 (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) ≤ 0.000117521303 ∧
    cc2 (rhoBar 13220 BstLean.Part154.csC) ≤ 0.000068222103 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13220 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13220 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13220 BstLean.Part154.csC * nuR (rhoBar 13220 BstLean.Part154.csC)) ≤ 0.000483626758 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241806070 : ℝ) * 0.000967282751 := by gcongr
      _ ≤ (0.000483626758 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13220 BstLean.Part154.csC) * nuR (rhoBar 13220 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967282751 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13220 BstLean.Part154.csC) * rhoBar 13220 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241806070 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241806070 / 2 + 0.399 * 0.000967282751 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184692764 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483626758 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117521303 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241806070 / 1.414213562 := by gcongr
      _ ≤ (0.000068222103 : ℝ) := by norm_num

end BstLean.Part269.N13220

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13220
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) ≤ 1.47311E-7 := by
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13220 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13220 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13220 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184692764 : ℝ) ^ 2 + 0.000117521303 ^ 2 + 3 * 0.000068222103 ^ 2 +
        2 * 0.797885 * 0.000184692764 * 0.000117521303 + 2 * 0.000184692764 * 0.000068222103 +
        4 * 0.797885 * 0.000117521303 * 0.000068222103 := by gcongr
    _ ≤ (1.47311E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13220 BstLean.Part154.csC Θ ≤ 0.002522362450 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13220 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13220 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13220 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035091757584 * 1.47311E-7 / (0.000241805696 : ℝ) := by gcongr
    _ ≤ 0.002522362450 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13220 BstLean.Part154.csC Θ ≤ 0.002796759715 + 0.000637362128 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13220 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13220 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035091757584 : ℝ) * ((2 * Θ * 0.000241806070 +
        (6863 / 10000) * 0.000241806070 * 13220 * 0.000967282751) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002796759715 + 0.000637362128 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13220 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13220 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13220 0.011 Θ ∧ gammaRatio 13220 0.011 Θ ≤ 0.000083126674 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13220 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035091757584 : ℝ) * 0.525 / ((1 - 0.011) * 13220) := by gcongr
      _ ≤ (0.000083126674 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13220 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13220 0.011 Θ) :=
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
    badAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13220 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13220 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13220 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13220 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13220 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13220 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13220 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13220 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13220 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13220 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035091757584 : ℝ) * 13220 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003114330481 + 0.003159724578 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13220

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13220
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13220 BstLean.Part154.csC) (piBar (rhoBar 13220 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13220 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13220 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13220 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13220 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13220 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13220 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13220 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13220 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13220 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13220 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051430659232 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13220) ≤ 0.010386638252 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13220 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035091757584)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010386638252 + 2 * 0.737676 / 13220) := by gcongr
    _ ≤ (0.051430659232 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13220 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13220

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13220
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526159251 : ℝ) ≤ plow 13220 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13220) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279785885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324240287) : eMP 13220 0.011 xi bn ≤ 0.001140731747 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13220 : ℝ) * (1 - 0.011))) ≤ 0.000564084914 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324240287 / (13220 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564084914 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564084914 : ℝ) + 3.141593 * 0.052279785885 / (13220 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140731747 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279785885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324240287) : PiBarMP 13220 12 0.011 xi bn ≤ 0.158016829608 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13220 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036390112490 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.344129713772 : ℝ) ≤ √((13220 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.978258814438 : ℝ) ≤ √(13220 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13220) ≤ 0.121174284656 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036390112490 + 0.052279785885 * 1.772454 / (2 * (114.344129713772 : ℝ))) * (1 + 0.001140731747) +
        8 / (13220 * 114.978258814438) + 0.121174284656 := by gcongr
    _ ≤ (0.158016829608 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279785885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324240287) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280078392405) :
    parallelOracle 13220 0.011 xi bn cd ≤ 0.158968762894 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13220 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13220 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526159251 : ℝ) ≤ plow 13220 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.978258814438 : ℝ) ≤ √(13220 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280078392405 : ℝ) / (2 * 0.560526159251 * 114.978258814438)) * 0.158016829608 +
        0.280078392405 ^ 2 / (2 * 0.560526159251 * 114.978258814438) := by gcongr
    _ ≤ (0.158968762894 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279785885) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324240287)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280078392405) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13220 13220 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526159251 : ℝ) ≤ plow 13220 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.978258814438 : ℝ) ≤ √(13220 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13220 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13220 Θ 1.22 ≤ 0.011533489146 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.978258814438 := by gcongr <;> linarith
      _ ≤ (0.011533489146 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13220 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13220 13220 0.011 ≤ 0.008313631589 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13220 13220 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13220 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13220 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13220 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13220 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158968762894 + 0.011533489146 + (0.008313631589 : ℝ) *
        (1 + 2 * (0.280078392405 + 0.011533489146) / (0.560526159251 * 114.978258814438))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13220]

end BstLean.Part269.N13220

/-! The original eight local profiles supply actual 13220 moment certificates. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13220 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052279785885 ∧
    0 ≤ bN 13220 BstLean.Part154.csC (groupTheta g) ∧ bN 13220 BstLean.Part154.csC (groupTheta g) ≤ 0.001324240287 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13220 13220 0.011
      (momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13220 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13220 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13220 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228647733173 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13220 0.011
      (momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13220 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13220
/-! The actual computed-centre upper energy formula at 13220. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13220

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13220)
open BstLean.Part268 (cell13220)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084102325573
  | 2 => 0.085024024978
  | 3 => 0.085940928234
  | 4 => 0.086853760620
  | 5 => 0.087763418537
  | 6 => 0.088670997216
  | 7 => 0.089577821478
  | 8 => 0.090485479676
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13220 13220 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13220 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13220

/-! Actual upper energy certificates on all 43 source endpoints at 13220. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13220)
open BstLean.Part268 (cell13220)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13220 (gMinus 13220) (1 - (cell13220 i).lower) ≤ 1 ∧
    energyUpper 13220 (gMinus 13220) (BstLean.Part211.gPlus 13220)
      (finiteEnergy 13220 13220 0.011) (1 - (cell13220 i).lower) ≤
      (cell13220 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨10,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨11,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨12,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨13,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨14,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨15,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨16,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨17,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨18,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨19,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨20,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨21,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨22,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨23,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨24,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨25,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨26,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨27,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨28,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨29,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨30,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨31,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨32,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨33,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨34,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨35,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨36,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨37,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨38,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨39,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨40,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨41,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨42,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨43,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨44,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨45,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨46,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨47,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨48,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨49,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨50,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨51,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13220) (by norm_num)
        (q := 1 - (cell13220 ⟨52,by decide⟩).lower)
        (by norm_num [cell13220]) (by norm_num [cell13220])
      exact ⟨E.1,E.2.trans (by norm_num [cell13220])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13220

/-! Source-cell containment and simple scalar guards at 13220. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13220)
open BstLean.Part268 (cell13220)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13220 ⟨10,by decide⟩).lower ∧ (cell13220 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13220 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13220 ⟨11,by decide⟩).lower ∧ (cell13220 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13220 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13220 ⟨12,by decide⟩).lower ∧ (cell13220 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13220 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13220 ⟨13,by decide⟩).lower ∧ (cell13220 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13220 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13220 ⟨14,by decide⟩).lower ∧ (cell13220 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13220 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13220 ⟨15,by decide⟩).lower ∧ (cell13220 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13220 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13220 ⟨16,by decide⟩).lower ∧ (cell13220 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13220 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13220 ⟨17,by decide⟩).lower ∧ (cell13220 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13220 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13220 ⟨18,by decide⟩).lower ∧ (cell13220 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13220 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13220 ⟨19,by decide⟩).lower ∧ (cell13220 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13220 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13220 ⟨20,by decide⟩).lower ∧ (cell13220 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13220 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13220 ⟨21,by decide⟩).lower ∧ (cell13220 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13220 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13220 ⟨22,by decide⟩).lower ∧ (cell13220 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13220 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13220 ⟨23,by decide⟩).lower ∧ (cell13220 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13220 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13220 ⟨24,by decide⟩).lower ∧ (cell13220 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13220 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13220 ⟨25,by decide⟩).lower ∧ (cell13220 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13220 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13220 ⟨26,by decide⟩).lower ∧ (cell13220 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13220 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13220 ⟨27,by decide⟩).lower ∧ (cell13220 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13220 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13220 ⟨28,by decide⟩).lower ∧ (cell13220 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13220 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13220 ⟨29,by decide⟩).lower ∧ (cell13220 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13220 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13220 ⟨30,by decide⟩).lower ∧ (cell13220 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13220 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13220 ⟨31,by decide⟩).lower ∧ (cell13220 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13220 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13220 ⟨32,by decide⟩).lower ∧ (cell13220 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13220 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13220 ⟨33,by decide⟩).lower ∧ (cell13220 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13220 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13220 ⟨34,by decide⟩).lower ∧ (cell13220 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13220 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13220 ⟨35,by decide⟩).lower ∧ (cell13220 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13220 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13220 ⟨36,by decide⟩).lower ∧ (cell13220 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13220 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13220 ⟨37,by decide⟩).lower ∧ (cell13220 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13220 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13220 ⟨38,by decide⟩).lower ∧ (cell13220 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13220 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13220 ⟨39,by decide⟩).lower ∧ (cell13220 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13220 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13220 ⟨40,by decide⟩).lower ∧ (cell13220 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13220 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13220 ⟨41,by decide⟩).lower ∧ (cell13220 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13220 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13220 ⟨42,by decide⟩).lower ∧ (cell13220 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13220 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13220 ⟨43,by decide⟩).lower ∧ (cell13220 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13220 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13220 ⟨44,by decide⟩).lower ∧ (cell13220 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13220 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13220 ⟨45,by decide⟩).lower ∧ (cell13220 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13220 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13220 ⟨46,by decide⟩).lower ∧ (cell13220 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13220 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13220 ⟨47,by decide⟩).lower ∧ (cell13220 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13220 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13220 ⟨48,by decide⟩).lower ∧ (cell13220 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13220 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13220 ⟨49,by decide⟩).lower ∧ (cell13220 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13220 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13220 ⟨50,by decide⟩).lower ∧ (cell13220 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13220 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13220 ⟨51,by decide⟩).lower ∧ (cell13220 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13220 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13220 ⟨52,by decide⟩).lower ∧ (cell13220 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13220 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13220 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13220 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13220,cell13220,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13220 i).lower ∧
    (cell13220 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13220 i).upper ≤ (0.532 : ℝ) ∧
    (cell13220 i).centre ≤ (0.1 : ℝ) ∧ (cell13220 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13220 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13220 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13220

/-! The local source numeric instances at 13220 have no network premises. -/
namespace BstLean.Part269.N13220
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13220)
open BstLean.Part268 (cell13220)

noncomputable def sourceNumerics13220 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13220 (cell13220 i)
      scalarRow13220.M scalarRow13220.H scalarRow13220.xi := by
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
    energy_allowance := scalarRow13220.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13220]
    centre_nonneg := (scalarRow13220.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13220])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13220
/-! Actual 13221 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13221 ≤ (1.035090418995 : ℝ) := by
  have hr : (114.982607380420 : ℝ) ≤ √(13221 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.982607380420 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13221 13221 (11 / 1000) ≤
    (0.008313317171 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13221) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.982607380420 : ℝ) ≤ √(13221 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13221)
  have hdiv : K / √(13221 : ℝ) ≤ K / 114.982607380420 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.982607380420 ≤ (0.008313317171 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13221.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13221 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13221 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13221 := gPlus_lower 13221
end BstLean.Part269.N13221

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13221
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035090418994 : ℝ) ≤ wn 13221 := by
  have hn : √(13221 : ℝ) ≤ 114.982607380421 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13221 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.982607380421 ≤ 2 / √(13221 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241787093 : ℝ) ≤ rhoBar 13221 BstLean.Part154.csC ∧
    rhoBar 13221 BstLean.Part154.csC ≤ 0.000241787468 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035090418994 : ℝ) / (1.295212 * 13221) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035090418995 : ℝ) / (1.29521 * 13221) := by gcongr
      _ ≤ (0.000241787468 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13221 BstLean.Part154.csC) ≤ 0.000967208334 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13221 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) ≤ 0.000184678555 ∧
    cc1 (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) ≤ 0.000117512262 ∧
    cc2 (rhoBar 13221 BstLean.Part154.csC) ≤ 0.000068216854 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13221 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13221 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13221 BstLean.Part154.csC * nuR (rhoBar 13221 BstLean.Part154.csC)) ≤ 0.000483589552 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241787468 : ℝ) * 0.000967208334 := by gcongr
      _ ≤ (0.000483589552 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13221 BstLean.Part154.csC) * nuR (rhoBar 13221 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967208334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13221 BstLean.Part154.csC) * rhoBar 13221 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241787468 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241787468 / 2 + 0.399 * 0.000967208334 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184678555 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483589552 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117512262 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241787468 / 1.414213562 := by gcongr
      _ ≤ (0.000068216854 : ℝ) := by norm_num

end BstLean.Part269.N13221

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13221
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) ≤ 1.47289E-7 := by
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13221 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13221 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13221 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184678555 : ℝ) ^ 2 + 0.000117512262 ^ 2 + 3 * 0.000068216854 ^ 2 +
        2 * 0.797885 * 0.000184678555 * 0.000117512262 + 2 * 0.000184678555 * 0.000068216854 +
        4 * 0.797885 * 0.000117512262 * 0.000068216854 := by gcongr
    _ ≤ (1.47289E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13221 BstLean.Part154.csC Θ ≤ 0.002522176529 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13221 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13221 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13221 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035090418995 * 1.47289E-7 / (0.000241787093 : ℝ) := by gcongr
    _ ≤ 0.002522176529 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13221 BstLean.Part154.csC Θ ≤ 0.002796537319 + 0.000637312272 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13221 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13221 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035090418995 : ℝ) * ((2 * Θ * 0.000241787468 +
        (6863 / 10000) * 0.000241787468 * 13221 * 0.000967208334) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002796537319 + 0.000637312272 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13221 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13221 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13221 0.011 Θ ∧ gammaRatio 13221 0.011 Θ ≤ 0.000083120279 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13221 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035090418995 : ℝ) * 0.525 / ((1 - 0.011) * 13221) := by gcongr
      _ ≤ (0.000083120279 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13221 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13221 0.011 Θ) :=
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
    badAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13221 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13221 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13221 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13221 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13221 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13221 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13221 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13221 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13221 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13221 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035090418995 : ℝ) * 13221 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003114108085 + 0.003159488801 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13221

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13221
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13221 BstLean.Part154.csC) (piBar (rhoBar 13221 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13221 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13221 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13221 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13221 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13221 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13221 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13221 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13221 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13221 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13221 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051428693482 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13221) ≤ 0.010386245436 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13221 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035090418995)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010386245436 + 2 * 0.737676 / 13221) := by gcongr
    _ ≤ (0.051428693482 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13221 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13221

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13221
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526200983 : ℝ) ≤ plow 13221 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13221) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279439706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324142678) : eMP 13221 0.011 xi bn ≤ 0.001140646470 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13221 : ℝ) * (1 - 0.011))) ≤ 0.000564042792 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324142678 / (13221 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564042792 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564042792 : ℝ) + 3.141593 * 0.052279439706 / (13221 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140646470 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279439706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324142678) : PiBarMP 13221 12 0.011 xi bn ≤ 0.158010882413 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13221 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036388771318 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.348454296505 : ℝ) ≤ √((13221 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.982607380420 : ℝ) ≤ √(13221 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13221) ≤ 0.121169701925 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036388771318 + 0.052279439706 * 1.772454 / (2 * (114.348454296505 : ℝ))) * (1 + 0.001140646470) +
        8 / (13221 * 114.982607380420) + 0.121169701925 := by gcongr
    _ ≤ (0.158010882413 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279439706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324142678) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280075669640) :
    parallelOracle 13221 0.011 xi bn cd ≤ 0.158962751535 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13221 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13221 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526200983 : ℝ) ≤ plow 13221 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.982607380420 : ℝ) ≤ √(13221 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280075669640 : ℝ) / (2 * 0.560526200983 * 114.982607380420)) * 0.158010882413 +
        0.280075669640 ^ 2 / (2 * 0.560526200983 * 114.982607380420) := by gcongr
    _ ≤ (0.158962751535 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279439706) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324142678)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280075669640) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13221 13221 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526200983 : ℝ) ≤ plow 13221 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.982607380420 : ℝ) ≤ √(13221 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13221 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13221 Θ 1.22 ≤ 0.011533052957 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.982607380420 := by gcongr <;> linarith
      _ ≤ (0.011533052957 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13221 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13221 13221 0.011 ≤ 0.008313317171 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13221 13221 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13221 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13221 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13221 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13221 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158962751535 + 0.011533052957 + (0.008313317171 : ℝ) *
        (1 + 2 * (0.280075669640 + 0.011533052957) / (0.560526200983 * 114.982607380420))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13221]

end BstLean.Part269.N13221

/-! The original eight local profiles supply actual 13221 moment certificates. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13221 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052279439706 ∧
    0 ≤ bN 13221 BstLean.Part154.csC (groupTheta g) ∧ bN 13221 BstLean.Part154.csC (groupTheta g) ≤ 0.001324142678 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13221 13221 0.011
      (momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13221 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13221 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13221 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228646976158 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13221 0.011
      (momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13221 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13221
/-! The actual computed-centre upper energy formula at 13221. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13221

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13221)
open BstLean.Part268 (cell13221)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084099868459
  | 2 => 0.085021538780
  | 3 => 0.085938409015
  | 4 => 0.086851203490
  | 5 => 0.087760817473
  | 6 => 0.088668344858
  | 7 => 0.089575108898
  | 8 => 0.090482696118
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13221 13221 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13221 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13221

/-! Actual upper energy certificates on all 43 source endpoints at 13221. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13221)
open BstLean.Part268 (cell13221)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13221 (gMinus 13221) (1 - (cell13221 i).lower) ≤ 1 ∧
    energyUpper 13221 (gMinus 13221) (BstLean.Part211.gPlus 13221)
      (finiteEnergy 13221 13221 0.011) (1 - (cell13221 i).lower) ≤
      (cell13221 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨10,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨11,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨12,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨13,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨14,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨15,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨16,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨17,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨18,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨19,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨20,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨21,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨22,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨23,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨24,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨25,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨26,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨27,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨28,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨29,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨30,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨31,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨32,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨33,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨34,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨35,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨36,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨37,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨38,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨39,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨40,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨41,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨42,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨43,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨44,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨45,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨46,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨47,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨48,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨49,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨50,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨51,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13221) (by norm_num)
        (q := 1 - (cell13221 ⟨52,by decide⟩).lower)
        (by norm_num [cell13221]) (by norm_num [cell13221])
      exact ⟨E.1,E.2.trans (by norm_num [cell13221])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13221

/-! Source-cell containment and simple scalar guards at 13221. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13221)
open BstLean.Part268 (cell13221)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13221 ⟨10,by decide⟩).lower ∧ (cell13221 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13221 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13221 ⟨11,by decide⟩).lower ∧ (cell13221 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13221 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13221 ⟨12,by decide⟩).lower ∧ (cell13221 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13221 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13221 ⟨13,by decide⟩).lower ∧ (cell13221 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13221 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13221 ⟨14,by decide⟩).lower ∧ (cell13221 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13221 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13221 ⟨15,by decide⟩).lower ∧ (cell13221 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13221 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13221 ⟨16,by decide⟩).lower ∧ (cell13221 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13221 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13221 ⟨17,by decide⟩).lower ∧ (cell13221 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13221 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13221 ⟨18,by decide⟩).lower ∧ (cell13221 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13221 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13221 ⟨19,by decide⟩).lower ∧ (cell13221 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13221 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13221 ⟨20,by decide⟩).lower ∧ (cell13221 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13221 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13221 ⟨21,by decide⟩).lower ∧ (cell13221 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13221 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13221 ⟨22,by decide⟩).lower ∧ (cell13221 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13221 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13221 ⟨23,by decide⟩).lower ∧ (cell13221 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13221 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13221 ⟨24,by decide⟩).lower ∧ (cell13221 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13221 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13221 ⟨25,by decide⟩).lower ∧ (cell13221 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13221 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13221 ⟨26,by decide⟩).lower ∧ (cell13221 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13221 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13221 ⟨27,by decide⟩).lower ∧ (cell13221 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13221 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13221 ⟨28,by decide⟩).lower ∧ (cell13221 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13221 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13221 ⟨29,by decide⟩).lower ∧ (cell13221 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13221 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13221 ⟨30,by decide⟩).lower ∧ (cell13221 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13221 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13221 ⟨31,by decide⟩).lower ∧ (cell13221 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13221 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13221 ⟨32,by decide⟩).lower ∧ (cell13221 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13221 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13221 ⟨33,by decide⟩).lower ∧ (cell13221 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13221 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13221 ⟨34,by decide⟩).lower ∧ (cell13221 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13221 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13221 ⟨35,by decide⟩).lower ∧ (cell13221 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13221 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13221 ⟨36,by decide⟩).lower ∧ (cell13221 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13221 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13221 ⟨37,by decide⟩).lower ∧ (cell13221 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13221 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13221 ⟨38,by decide⟩).lower ∧ (cell13221 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13221 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13221 ⟨39,by decide⟩).lower ∧ (cell13221 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13221 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13221 ⟨40,by decide⟩).lower ∧ (cell13221 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13221 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13221 ⟨41,by decide⟩).lower ∧ (cell13221 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13221 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13221 ⟨42,by decide⟩).lower ∧ (cell13221 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13221 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13221 ⟨43,by decide⟩).lower ∧ (cell13221 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13221 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13221 ⟨44,by decide⟩).lower ∧ (cell13221 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13221 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13221 ⟨45,by decide⟩).lower ∧ (cell13221 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13221 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13221 ⟨46,by decide⟩).lower ∧ (cell13221 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13221 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13221 ⟨47,by decide⟩).lower ∧ (cell13221 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13221 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13221 ⟨48,by decide⟩).lower ∧ (cell13221 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13221 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13221 ⟨49,by decide⟩).lower ∧ (cell13221 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13221 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13221 ⟨50,by decide⟩).lower ∧ (cell13221 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13221 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13221 ⟨51,by decide⟩).lower ∧ (cell13221 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13221 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13221 ⟨52,by decide⟩).lower ∧ (cell13221 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13221 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13221 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13221 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13221,cell13221,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13221 i).lower ∧
    (cell13221 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13221 i).upper ≤ (0.532 : ℝ) ∧
    (cell13221 i).centre ≤ (0.1 : ℝ) ∧ (cell13221 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13221 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13221 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13221

/-! The local source numeric instances at 13221 have no network premises. -/
namespace BstLean.Part269.N13221
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13221)
open BstLean.Part268 (cell13221)

noncomputable def sourceNumerics13221 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13221 (cell13221 i)
      scalarRow13221.M scalarRow13221.H scalarRow13221.xi := by
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
    energy_allowance := scalarRow13221.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13221]
    centre_nonneg := (scalarRow13221.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13221])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13221
/-! Actual 13222 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13222 ≤ (1.035089080558 : ℝ) := by
  have hr : (114.986955781949 : ℝ) ≤ √(13222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.986955781949 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13222 13222 (11 / 1000) ≤
    (0.008313002788 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13222) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.986955781949 : ℝ) ≤ √(13222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13222)
  have hdiv : K / √(13222 : ℝ) ≤ K / 114.986955781949 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.986955781949 ≤ (0.008313002788 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13222.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13222 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13222 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13222 := gPlus_lower 13222
end BstLean.Part269.N13222

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13222
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035089080557 : ℝ) ≤ wn 13222 := by
  have hn : √(13222 : ℝ) ≤ 114.986955781950 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13222 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.986955781950 ≤ 2 / √(13222 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241768494 : ℝ) ≤ rhoBar 13222 BstLean.Part154.csC ∧
    rhoBar 13222 BstLean.Part154.csC ≤ 0.000241768868 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035089080557 : ℝ) / (1.295212 * 13222) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035089080558 : ℝ) / (1.29521 * 13222) := by gcongr
      _ ≤ (0.000241768868 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13222 BstLean.Part154.csC) ≤ 0.000967133925 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13222 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) ≤ 0.000184664348 ∧
    cc1 (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) ≤ 0.000117503222 ∧
    cc2 (rhoBar 13222 BstLean.Part154.csC) ≤ 0.000068211607 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13222 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13222 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13222 BstLean.Part154.csC * nuR (rhoBar 13222 BstLean.Part154.csC)) ≤ 0.000483552350 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241768868 : ℝ) * 0.000967133925 := by gcongr
      _ ≤ (0.000483552350 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13222 BstLean.Part154.csC) * nuR (rhoBar 13222 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967133925 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13222 BstLean.Part154.csC) * rhoBar 13222 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241768868 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241768868 / 2 + 0.399 * 0.000967133925 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184664348 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483552350 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117503222 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241768868 / 1.414213562 := by gcongr
      _ ≤ (0.000068211607 : ℝ) := by norm_num

end BstLean.Part269.N13222

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13222
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) ≤ 1.47266E-7 := by
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13222 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13222 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13222 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184664348 : ℝ) ^ 2 + 0.000117503222 ^ 2 + 3 * 0.000068211607 ^ 2 +
        2 * 0.797885 * 0.000184664348 * 0.000117503222 + 2 * 0.000184664348 * 0.000068211607 +
        4 * 0.797885 * 0.000117503222 * 0.000068211607 := by gcongr
    _ ≤ (1.47266E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13222 BstLean.Part154.csC Θ ≤ 0.002521973414 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13222 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13222 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13222 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035089080558 * 1.47266E-7 / (0.000241768494 : ℝ) := by gcongr
    _ ≤ 0.002521973414 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13222 BstLean.Part154.csC Θ ≤ 0.002796314938 + 0.000637262421 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13222 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13222 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035089080558 : ℝ) * ((2 * Θ * 0.000241768868 +
        (6863 / 10000) * 0.000241768868 * 13222 * 0.000967133925) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002796314938 + 0.000637262421 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13222 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13222 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13222 0.011 Θ ∧ gammaRatio 13222 0.011 Θ ≤ 0.000083113885 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13222 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035089080558 : ℝ) * 0.525 / ((1 - 0.011) * 13222) := by gcongr
      _ ≤ (0.000083113885 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13222 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13222 0.011 Θ) :=
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
    badAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13222 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13222 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13222 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13222 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13222 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13222 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13222 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13222 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13222 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13222 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035089080558 : ℝ) * 13222 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003113885704 + 0.003159235835 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13222

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13222
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13222 BstLean.Part154.csC) (piBar (rhoBar 13222 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13222 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13222 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13222 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13222 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13222 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13222 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13222 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13222 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13222 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13222 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051426727958 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13222) ≤ 0.010385852665 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13222 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035089080558)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010385852665 + 2 * 0.737676 / 13222) := by gcongr
    _ ≤ (0.051426727958 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13222 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13222

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13222
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526242709 : ℝ) ≤ plow 13222 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13222) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279084518)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324036043) : eMP 13222 0.011 xi bn ≤ 0.001140557352 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13222 : ℝ) * (1 - 0.011))) ≤ 0.000563998751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001324036043 / (13222 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000563998751 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000563998751 : ℝ) + 3.141593 * 0.052279084518 / (13222 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140557352 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279084518)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324036043) : PiBarMP 13222 12 0.011 xi bn ≤ 0.158004811310 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13222 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036387306070 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.352778715691 : ℝ) ≤ √((13222 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.986955781949 : ℝ) ≤ √(13222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13222) ≤ 0.121165119713 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036387306070 + 0.052279084518 * 1.772454 / (2 * (114.352778715691 : ℝ))) * (1 + 0.001140557352) +
        8 / (13222 * 114.986955781949) + 0.121165119713 := by gcongr
    _ ≤ (0.158004811310 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279084518)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324036043) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280072927398) :
    parallelOracle 13222 0.011 xi bn cd ≤ 0.158956615897 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13222 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13222 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526242709 : ℝ) ≤ plow 13222 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.986955781949 : ℝ) ≤ √(13222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280072927398 : ℝ) / (2 * 0.560526242709 * 114.986955781949)) * 0.158004811310 +
        0.280072927398 ^ 2 / (2 * 0.560526242709 * 114.986955781949) := by gcongr
    _ ≤ (0.158956615897 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052279084518) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001324036043)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280072927398) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13222 13222 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526242709 : ℝ) ≤ plow 13222 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.986955781949 : ℝ) ≤ √(13222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13222 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13222 Θ 1.22 ≤ 0.011532616818 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.986955781949 := by gcongr <;> linarith
      _ ≤ (0.011532616818 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13222 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13222 13222 0.011 ≤ 0.008313002788 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13222 13222 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13222 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13222 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13222 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13222 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158956615897 + 0.011532616818 + (0.008313002788 : ℝ) *
        (1 + 2 * (0.280072927398 + 0.011532616818) / (0.560526242709 * 114.986955781949))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13222]

end BstLean.Part269.N13222

/-! The original eight local profiles supply actual 13222 moment certificates. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13222 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052279084518 ∧
    0 ≤ bN 13222 BstLean.Part154.csC (groupTheta g) ∧ bN 13222 BstLean.Part154.csC (groupTheta g) ≤ 0.001324036043 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13222 13222 0.011
      (momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13222 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13222 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13222 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228646199440 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13222 0.011
      (momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13222 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13222
/-! The actual computed-centre upper energy formula at 13222. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13222

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13222)
open BstLean.Part268 (cell13222)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084097412008
  | 2 => 0.085019053267
  | 3 => 0.085935890507
  | 4 => 0.086848647104
  | 5 => 0.087758217194
  | 6 => 0.088665693335
  | 7 => 0.089572397214
  | 8 => 0.090479913528
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13222 13222 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13222 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13222

/-! Actual upper energy certificates on all 43 source endpoints at 13222. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13222)
open BstLean.Part268 (cell13222)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13222 (gMinus 13222) (1 - (cell13222 i).lower) ≤ 1 ∧
    energyUpper 13222 (gMinus 13222) (BstLean.Part211.gPlus 13222)
      (finiteEnergy 13222 13222 0.011) (1 - (cell13222 i).lower) ≤
      (cell13222 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨10,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨11,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨12,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨13,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨14,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨15,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨16,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨17,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨18,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨19,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨20,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨21,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨22,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨23,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨24,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨25,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨26,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨27,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨28,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨29,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨30,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨31,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨32,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨33,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨34,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨35,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨36,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨37,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨38,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨39,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨40,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨41,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨42,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨43,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨44,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨45,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨46,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨47,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨48,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨49,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨50,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨51,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13222) (by norm_num)
        (q := 1 - (cell13222 ⟨52,by decide⟩).lower)
        (by norm_num [cell13222]) (by norm_num [cell13222])
      exact ⟨E.1,E.2.trans (by norm_num [cell13222])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13222

/-! Source-cell containment and simple scalar guards at 13222. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13222)
open BstLean.Part268 (cell13222)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13222 ⟨10,by decide⟩).lower ∧ (cell13222 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13222 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13222 ⟨11,by decide⟩).lower ∧ (cell13222 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13222 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13222 ⟨12,by decide⟩).lower ∧ (cell13222 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13222 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13222 ⟨13,by decide⟩).lower ∧ (cell13222 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13222 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13222 ⟨14,by decide⟩).lower ∧ (cell13222 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13222 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13222 ⟨15,by decide⟩).lower ∧ (cell13222 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13222 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13222 ⟨16,by decide⟩).lower ∧ (cell13222 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13222 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13222 ⟨17,by decide⟩).lower ∧ (cell13222 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13222 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13222 ⟨18,by decide⟩).lower ∧ (cell13222 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13222 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13222 ⟨19,by decide⟩).lower ∧ (cell13222 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13222 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13222 ⟨20,by decide⟩).lower ∧ (cell13222 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13222 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13222 ⟨21,by decide⟩).lower ∧ (cell13222 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13222 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13222 ⟨22,by decide⟩).lower ∧ (cell13222 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13222 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13222 ⟨23,by decide⟩).lower ∧ (cell13222 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13222 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13222 ⟨24,by decide⟩).lower ∧ (cell13222 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13222 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13222 ⟨25,by decide⟩).lower ∧ (cell13222 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13222 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13222 ⟨26,by decide⟩).lower ∧ (cell13222 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13222 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13222 ⟨27,by decide⟩).lower ∧ (cell13222 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13222 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13222 ⟨28,by decide⟩).lower ∧ (cell13222 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13222 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13222 ⟨29,by decide⟩).lower ∧ (cell13222 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13222 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13222 ⟨30,by decide⟩).lower ∧ (cell13222 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13222 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13222 ⟨31,by decide⟩).lower ∧ (cell13222 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13222 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13222 ⟨32,by decide⟩).lower ∧ (cell13222 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13222 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13222 ⟨33,by decide⟩).lower ∧ (cell13222 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13222 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13222 ⟨34,by decide⟩).lower ∧ (cell13222 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13222 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13222 ⟨35,by decide⟩).lower ∧ (cell13222 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13222 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13222 ⟨36,by decide⟩).lower ∧ (cell13222 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13222 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13222 ⟨37,by decide⟩).lower ∧ (cell13222 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13222 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13222 ⟨38,by decide⟩).lower ∧ (cell13222 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13222 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13222 ⟨39,by decide⟩).lower ∧ (cell13222 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13222 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13222 ⟨40,by decide⟩).lower ∧ (cell13222 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13222 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13222 ⟨41,by decide⟩).lower ∧ (cell13222 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13222 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13222 ⟨42,by decide⟩).lower ∧ (cell13222 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13222 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13222 ⟨43,by decide⟩).lower ∧ (cell13222 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13222 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13222 ⟨44,by decide⟩).lower ∧ (cell13222 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13222 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13222 ⟨45,by decide⟩).lower ∧ (cell13222 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13222 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13222 ⟨46,by decide⟩).lower ∧ (cell13222 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13222 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13222 ⟨47,by decide⟩).lower ∧ (cell13222 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13222 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13222 ⟨48,by decide⟩).lower ∧ (cell13222 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13222 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13222 ⟨49,by decide⟩).lower ∧ (cell13222 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13222 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13222 ⟨50,by decide⟩).lower ∧ (cell13222 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13222 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13222 ⟨51,by decide⟩).lower ∧ (cell13222 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13222 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13222 ⟨52,by decide⟩).lower ∧ (cell13222 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13222 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13222 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13222 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13222,cell13222,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13222 i).lower ∧
    (cell13222 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13222 i).upper ≤ (0.532 : ℝ) ∧
    (cell13222 i).centre ≤ (0.1 : ℝ) ∧ (cell13222 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13222 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13222 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13222

/-! The local source numeric instances at 13222 have no network premises. -/
namespace BstLean.Part269.N13222
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13222)
open BstLean.Part268 (cell13222)

noncomputable def sourceNumerics13222 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13222 (cell13222 i)
      scalarRow13222.M scalarRow13222.H scalarRow13222.xi := by
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
    energy_allowance := scalarRow13222.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13222]
    centre_nonneg := (scalarRow13222.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13222])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13222
/-! Actual 13223 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13223 ≤ (1.035087742274 : ℝ) := by
  have hr : (114.991304019043 : ℝ) ≤ √(13223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.991304019043 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13223 13223 (11 / 1000) ≤
    (0.008312688441 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13223) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.991304019043 : ℝ) ≤ √(13223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13223)
  have hdiv : K / √(13223 : ℝ) ≤ K / 114.991304019043 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.991304019043 ≤ (0.008312688441 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13223.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13223 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13223 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13223 := gPlus_lower 13223
end BstLean.Part269.N13223

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13223
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035087742273 : ℝ) ≤ wn 13223 := by
  have hn : √(13223 : ℝ) ≤ 114.991304019044 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13223 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.991304019044 ≤ 2 / √(13223 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000241749898 : ℝ) ≤ rhoBar 13223 BstLean.Part154.csC ∧
    rhoBar 13223 BstLean.Part154.csC ≤ 0.000241750272 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035087742273 : ℝ) / (1.295212 * 13223) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035087742274 : ℝ) / (1.29521 * 13223) := by gcongr
      _ ≤ (0.000241750272 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13223 BstLean.Part154.csC) ≤ 0.000967059532 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13223 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) ≤ 0.000184650143 ∧
    cc1 (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) ≤ 0.000117494183 ∧
    cc2 (rhoBar 13223 BstLean.Part154.csC) ≤ 0.000068206360 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13223 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13223 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13223 BstLean.Part154.csC * nuR (rhoBar 13223 BstLean.Part154.csC)) ≤ 0.000483515155 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241750272 : ℝ) * 0.000967059532 := by gcongr
      _ ≤ (0.000483515155 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13223 BstLean.Part154.csC) * nuR (rhoBar 13223 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000967059532 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13223 BstLean.Part154.csC) * rhoBar 13223 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241750272 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241750272 / 2 + 0.399 * 0.000967059532 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184650143 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483515155 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117494183 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241750272 / 1.414213562 := by gcongr
      _ ≤ (0.000068206360 : ℝ) := by norm_num

end BstLean.Part269.N13223

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13223
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) ≤ 1.47243E-7 := by
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13223 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13223 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13223 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184650143 : ℝ) ^ 2 + 0.000117494183 ^ 2 + 3 * 0.000068206360 ^ 2 +
        2 * 0.797885 * 0.000184650143 * 0.000117494183 + 2 * 0.000184650143 * 0.000068206360 +
        4 * 0.797885 * 0.000117494183 * 0.000068206360 := by gcongr
    _ ≤ (1.47243E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13223 BstLean.Part154.csC Θ ≤ 0.002521770238 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13223 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13223 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13223 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035087742274 * 1.47243E-7 / (0.000241749898 : ℝ) := by gcongr
    _ ≤ 0.002521770238 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13223 BstLean.Part154.csC Θ ≤ 0.002796092618 + 0.000637212581 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13223 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13223 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035087742274 : ℝ) * ((2 * Θ * 0.000241750272 +
        (6863 / 10000) * 0.000241750272 * 13223 * 0.000967059532) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002796092618 + 0.000637212581 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13223 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13223 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13223 0.011 Θ ∧ gammaRatio 13223 0.011 Θ ≤ 0.000083107492 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13223 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035087742274 : ℝ) * 0.525 / ((1 - 0.011) * 13223) := by gcongr
      _ ≤ (0.000083107492 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13223 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13223 0.011 Θ) :=
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
    badAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317570766 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13223 BstLean.Part154.csC) 1.22 ≤ 1.0209E-8 := by
    have he : (18.4 : ℝ) ≤ gap 2 (rhoBar 13223 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13223 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13223 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13223 0.011 Θ) 1.12 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 1 (gammaRatio 13223 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13223 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13223 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13223 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13223 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035087742274 : ℝ) * 13223 *
        (1.0209E-8 / 1.1045361 + 1.2470E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317570766 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003113663384 + 0.003158982819 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13223

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13223
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13223 BstLean.Part154.csC) (piBar (rhoBar 13223 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13223 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13223 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13223 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13223 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13223 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13223 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13223 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13223 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13223 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13223 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051424762656 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13223) ≤ 0.010385459938 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13223 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035087742274)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010385459938 + 2 * 0.737676 / 13223) := by gcongr
    _ ≤ (0.051424762656 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13223 12 ≤ 0.0015 := by
  exact BstLean.Part269.S34.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13223

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13223
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526284428 : ℝ) ≤ plow 13223 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13223) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052278729364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323929375) : eMP 13223 0.011 xi bn ≤ 0.001140468227 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13223 : ℝ) * (1 - 0.011))) ≤ 0.000563954706 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001323929375 / (13223 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000563954706 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000563954706 : ℝ) + 3.141593 * 0.052278729364 / (13223 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140468227 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052278729364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323929375) : PiBarMP 13223 12 0.011 xi bn ≤ 0.157998740218 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13223 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036385840310 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.357102971350 : ℝ) ≤ √((13223 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.991304019043 : ℝ) ≤ √(13223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13223) ≤ 0.121160538022 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036385840310 + 0.052278729364 * 1.772454 / (2 * (114.357102971350 : ℝ))) * (1 + 0.001140468227) +
        8 / (13223 * 114.991304019043) + 0.121160538022 := by gcongr
    _ ≤ (0.157998740218 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052278729364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323929375) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280070185449) :
    parallelOracle 13223 0.011 xi bn cd ≤ 0.158950480278 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13223 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13223 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526284428 : ℝ) ≤ plow 13223 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.991304019043 : ℝ) ≤ √(13223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280070185449 : ℝ) / (2 * 0.560526284428 * 114.991304019043)) * 0.157998740218 +
        0.280070185449 ^ 2 / (2 * 0.560526284428 * 114.991304019043) := by gcongr
    _ ≤ (0.158950480278 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052278729364) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323929375)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280070185449) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13223 13223 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526284428 : ℝ) ≤ plow 13223 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.991304019043 : ℝ) ≤ √(13223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13223 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13223 Θ 1.22 ≤ 0.011532180728 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.991304019043 := by gcongr <;> linarith
      _ ≤ (0.011532180728 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13223 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13223 13223 0.011 ≤ 0.008312688441 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13223 13223 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13223 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13223 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13223 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13223 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158950480278 + 0.011532180728 + (0.008312688441 : ℝ) *
        (1 + 2 * (0.280070185449 + 0.011532180728) / (0.560526284428 * 114.991304019043))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13223]

end BstLean.Part269.N13223

/-! The original eight local profiles supply actual 13223 moment certificates. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13223 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052278729364 ∧
    0 ≤ bN 13223 BstLean.Part154.csC (groupTheta g) ∧ bN 13223 BstLean.Part154.csC (groupTheta g) ≤ 0.001323929375 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13223 13223 0.011
      (momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13223 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13223 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13223 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228645422793 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13223 0.011
      (momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13223 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13223
/-! The actual computed-centre upper energy formula at 13223. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13223

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13223)
open BstLean.Part268 (cell13223)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084094956221
  | 2 => 0.085016568438
  | 3 => 0.085933372711
  | 4 => 0.086846091463
  | 5 => 0.087755617700
  | 6 => 0.088663042646
  | 7 => 0.089569686424
  | 8 => 0.090477131907
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13223 13223 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13223 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003118785860 + 0.003164686405 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S34.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S34.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13223

/-! Actual upper energy certificates on all 43 source endpoints at 13223. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13223)
open BstLean.Part268 (cell13223)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13223 (gMinus 13223) (1 - (cell13223 i).lower) ≤ 1 ∧
    energyUpper 13223 (gMinus 13223) (BstLean.Part211.gPlus 13223)
      (finiteEnergy 13223 13223 0.011) (1 - (cell13223 i).lower) ≤
      (cell13223 i).energy := by
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
      have E := BstLean.Part269.S34.uniformEnergy10 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨10,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy11 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨11,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy12 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨12,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy13 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨13,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy14 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨14,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy15 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨15,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy16 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨16,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy17 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨17,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy18 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨18,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy19 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨19,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy20 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨20,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy21 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨21,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy22 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨22,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy23 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨23,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy24 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨24,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy25 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨25,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy26 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨26,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy27 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨27,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy28 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨28,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy29 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨29,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy30 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨30,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy31 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨31,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy32 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨32,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy33 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨33,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy34 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨34,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy35 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨35,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy36 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨36,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy37 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨37,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy38 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨38,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy39 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨39,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy40 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨40,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy41 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨41,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy42 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨42,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy43 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨43,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy44 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨44,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy45 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨45,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy46 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨46,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy47 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨47,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy48 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨48,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy49 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨49,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy50 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨50,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy51 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨51,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S34.uniformEnergy52 (n := 13223) (by norm_num)
        (q := 1 - (cell13223 ⟨52,by decide⟩).lower)
        (by norm_num [cell13223]) (by norm_num [cell13223])
      exact ⟨E.1,E.2.trans (by norm_num [cell13223])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13223

/-! Source-cell containment and simple scalar guards at 13223. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13223)
open BstLean.Part268 (cell13223)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13223 ⟨10,by decide⟩).lower ∧ (cell13223 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13223 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13223 ⟨11,by decide⟩).lower ∧ (cell13223 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13223 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13223 ⟨12,by decide⟩).lower ∧ (cell13223 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13223 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13223 ⟨13,by decide⟩).lower ∧ (cell13223 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13223 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13223 ⟨14,by decide⟩).lower ∧ (cell13223 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13223 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13223 ⟨15,by decide⟩).lower ∧ (cell13223 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13223 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13223 ⟨16,by decide⟩).lower ∧ (cell13223 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13223 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13223 ⟨17,by decide⟩).lower ∧ (cell13223 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13223 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13223 ⟨18,by decide⟩).lower ∧ (cell13223 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13223 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13223 ⟨19,by decide⟩).lower ∧ (cell13223 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13223 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13223 ⟨20,by decide⟩).lower ∧ (cell13223 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13223 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13223 ⟨21,by decide⟩).lower ∧ (cell13223 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13223 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13223 ⟨22,by decide⟩).lower ∧ (cell13223 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13223 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13223 ⟨23,by decide⟩).lower ∧ (cell13223 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13223 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13223 ⟨24,by decide⟩).lower ∧ (cell13223 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13223 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13223 ⟨25,by decide⟩).lower ∧ (cell13223 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13223 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13223 ⟨26,by decide⟩).lower ∧ (cell13223 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13223 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13223 ⟨27,by decide⟩).lower ∧ (cell13223 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13223 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13223 ⟨28,by decide⟩).lower ∧ (cell13223 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13223 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13223 ⟨29,by decide⟩).lower ∧ (cell13223 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13223 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13223 ⟨30,by decide⟩).lower ∧ (cell13223 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13223 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13223 ⟨31,by decide⟩).lower ∧ (cell13223 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13223 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13223 ⟨32,by decide⟩).lower ∧ (cell13223 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13223 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13223 ⟨33,by decide⟩).lower ∧ (cell13223 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13223 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13223 ⟨34,by decide⟩).lower ∧ (cell13223 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13223 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13223 ⟨35,by decide⟩).lower ∧ (cell13223 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13223 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13223 ⟨36,by decide⟩).lower ∧ (cell13223 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13223 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13223 ⟨37,by decide⟩).lower ∧ (cell13223 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13223 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13223 ⟨38,by decide⟩).lower ∧ (cell13223 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13223 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13223 ⟨39,by decide⟩).lower ∧ (cell13223 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13223 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13223 ⟨40,by decide⟩).lower ∧ (cell13223 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13223 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13223 ⟨41,by decide⟩).lower ∧ (cell13223 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13223 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13223 ⟨42,by decide⟩).lower ∧ (cell13223 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13223 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13223 ⟨43,by decide⟩).lower ∧ (cell13223 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13223 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13223 ⟨44,by decide⟩).lower ∧ (cell13223 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13223 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13223 ⟨45,by decide⟩).lower ∧ (cell13223 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13223 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13223 ⟨46,by decide⟩).lower ∧ (cell13223 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13223 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13223 ⟨47,by decide⟩).lower ∧ (cell13223 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13223 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13223 ⟨48,by decide⟩).lower ∧ (cell13223 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13223 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13223 ⟨49,by decide⟩).lower ∧ (cell13223 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13223 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13223 ⟨50,by decide⟩).lower ∧ (cell13223 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13223 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13223 ⟨51,by decide⟩).lower ∧ (cell13223 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13223 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13223 ⟨52,by decide⟩).lower ∧ (cell13223 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13223 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13223 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13223 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13223,cell13223,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13223 i).lower ∧
    (cell13223 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13223 i).upper ≤ (0.532 : ℝ) ∧
    (cell13223 i).centre ≤ (0.1 : ℝ) ∧ (cell13223 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13223 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13223 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13223

/-! The local source numeric instances at 13223 have no network premises. -/
namespace BstLean.Part269.N13223
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13223)
open BstLean.Part268 (cell13223)

noncomputable def sourceNumerics13223 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13223 (cell13223 i)
      scalarRow13223.M scalarRow13223.H scalarRow13223.xi := by
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
    energy_allowance := scalarRow13223.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13223]
    centre_nonneg := (scalarRow13223.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13223])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13223