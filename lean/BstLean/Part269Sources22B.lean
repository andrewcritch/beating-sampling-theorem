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
import BstLean.Part269Direction22
import BstLean.Part269Shared22
import BstLean.Part269Finite
import BstLean.Part269Rows22
import BstLean.Part269Source
/-! Actual 12913 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12913 ≤ (1.035510069485 : ℝ) := by
  have hr : (113.635381813940 : ℝ) ≤ √(12913 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.635381813940 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12913 12913 (11 / 1000) ≤
    (0.008411878002 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12913) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.635381813940 : ℝ) ≤ √(12913 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12913)
  have hdiv : K / √(12913 : ℝ) ≤ K / 113.635381813940 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.635381813940 ≤ (0.008411878002 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12913.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12913 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12913 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12913 := gPlus_lower 12913
end BstLean.Part269.N12913

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12913
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035510069484 : ℝ) ≤ wn 12913 := by
  have hn : √(12913 : ℝ) ≤ 113.635381813941 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12913 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.635381813941 ≤ 2 / √(12913 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247654547 : ℝ) ≤ rhoBar 12913 BstLean.Part154.csC ∧
    rhoBar 12913 BstLean.Part154.csC ≤ 0.000247654931 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035510069484 : ℝ) / (1.295212 * 12913) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035510069485 : ℝ) / (1.29521 * 12913) := by gcongr
      _ ≤ (0.000247654931 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12913 BstLean.Part154.csC) ≤ 0.000990681057 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12913 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) ≤ 0.000189160359 ∧
    cc1 (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) ≤ 0.000120364023 ∧
    cc2 (rhoBar 12913 BstLean.Part154.csC) ≤ 0.000069872274 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12913 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12913 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12913 BstLean.Part154.csC * nuR (rhoBar 12913 BstLean.Part154.csC)) ≤ 0.000495325196 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247654931 : ℝ) * 0.000990681057 := by gcongr
      _ ≤ (0.000495325196 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12913 BstLean.Part154.csC) * nuR (rhoBar 12913 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990681057 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12913 BstLean.Part154.csC) * rhoBar 12913 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247654931 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247654931 / 2 + 0.399 * 0.000990681057 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189160359 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495325196 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120364023 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247654931 / 1.414213562 := by gcongr
      _ ≤ (0.000069872274 : ℝ) := by norm_num

end BstLean.Part269.N12913

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12913
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) ≤ 1.54524E-7 := by
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12913 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12913 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12913 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189160359 : ℝ) ^ 2 + 0.000120364023 ^ 2 + 3 * 0.000069872274 ^ 2 +
        2 * 0.797885 * 0.000189160359 * 0.000120364023 + 2 * 0.000189160359 * 0.000069872274 +
        4 * 0.797885 * 0.000120364023 * 0.000069872274 := by gcongr
    _ ≤ (1.54524E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12913 BstLean.Part154.csC Θ ≤ 0.002584425119 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12913 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12913 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12913 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035510069485 * 1.54524E-7 / (0.000247654547 : ℝ) := by gcongr
    _ ≤ 0.002584425119 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12913 BstLean.Part154.csC Θ ≤ 0.002866728234 + 0.000653042598 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12913 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12913 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035510069485 : ℝ) * ((2 * Θ * 0.000247654931 +
        (6863 / 10000) * 0.000247654931 * 12913 * 0.000990681057) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002866728234 + 0.000653042598 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12913 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12913 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12913 0.011 Θ ∧ gammaRatio 12913 0.011 Θ ≤ 0.000085137361 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12913 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035510069485 : ℝ) * 0.525 / ((1 - 0.011) * 12913) := by gcongr
      _ ≤ (0.000085137361 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12913 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12913 0.011 Θ) :=
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
    badAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12913 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12913 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12913 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12913 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12913 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12913 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12913 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12913 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12913 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12913 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035510069485 : ℝ) * 12913 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003330399251 + 0.003237467717 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12913

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12913
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12913 BstLean.Part154.csC) (piBar (rhoBar 12913 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12913 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12913 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12913 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12913 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12913 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12913 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12913 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12913 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12913 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12913 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052044974159 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12913) ≤ 0.010509381515 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12913 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035510069485)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010509381515 + 2 * 0.737676 / 12913) := by gcongr
    _ ≤ (0.052044974159 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12913 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12913

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12913
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513041895 : ℝ) ≤ plow 12913 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12913) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536669803)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356823188) : eMP 12913 0.011 xi bn ≤ 0.001168383626 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12913 : ℝ) * (1 - 0.011))) ≤ 0.000577729931 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356823188 / (12913 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577729931 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577729931 : ℝ) + 3.141593 * 0.052536669803 / (12913 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168383626 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536669803)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356823188) : PiBarMP 12913 12 0.011 xi bn ≤ 0.159902302426 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12913 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036835080942 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.008658960276 : ℝ) ≤ √((12913 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.635381813940 : ℝ) ≤ √(12913 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12913) ≤ 0.122606252035 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036835080942 + 0.052536669803 * 1.772454 / (2 * (113.008658960276 : ℝ))) * (1 + 0.001168383626) +
        8 / (12913 * 113.635381813940) + 0.122606252035 := by gcongr
    _ ≤ (0.159902302426 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536669803)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356823188) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281253765010) :
    parallelOracle 12913 0.011 xi bn cd ≤ 0.160876307700 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12913 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12913 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513041895 : ℝ) ≤ plow 12913 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.635381813940 : ℝ) ≤ √(12913 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281253765010 : ℝ) / (2 * 0.560513041895 * 113.635381813940)) * 0.159902302426 +
        0.281253765010 ^ 2 / (2 * 0.560513041895 * 113.635381813940) := by gcongr
    _ ≤ (0.160876307700 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536669803) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356823188)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281253765010) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12913 12913 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513041895 : ℝ) ≤ plow 12913 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.635381813940 : ℝ) ≤ √(12913 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12913 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12913 Θ 1.22 ≤ 0.011669785228 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.635381813940 := by gcongr <;> linarith
      _ ≤ (0.011669785228 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12913 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12913 12913 0.011 ≤ 0.008411878002 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12913 12913 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12913 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12913 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12913 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12913 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160876307700 + 0.011669785228 + (0.008411878002 : ℝ) *
        (1 + 2 * (0.281253765010 + 0.011669785228) / (0.560513041895 * 113.635381813940))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12913]

end BstLean.Part269.N12913

/-! The original eight local profiles supply actual 12913 moment certificates. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12913 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052536669803 ∧
    0 ≤ bN 12913 BstLean.Part154.csC (groupTheta g) ∧ bN 12913 BstLean.Part154.csC (groupTheta g) ≤ 0.001356823188 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12913 12913 0.011
      (momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12913 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12913 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12913 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229208790851 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12913 0.011
      (momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12913 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12913
/-! The actual computed-centre upper energy formula at 12913. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12913

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12913)
open BstLean.Part268 (cell12913)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084892020741
  | 2 => 0.085824280391
  | 3 => 0.086753231803
  | 4 => 0.087679954034
  | 5 => 0.088605762526
  | 6 => 0.089532245505
  | 7 => 0.090461304051
  | 8 => 0.091395195923
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12913 12913 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12913 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12913

/-! Actual upper energy certificates on all 43 source endpoints at 12913. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12913)
open BstLean.Part268 (cell12913)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12913 (gMinus 12913) (1 - (cell12913 i).lower) ≤ 1 ∧
    energyUpper 12913 (gMinus 12913) (BstLean.Part211.gPlus 12913)
      (finiteEnergy 12913 12913 0.011) (1 - (cell12913 i).lower) ≤
      (cell12913 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨10,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨11,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨12,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨13,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨14,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨15,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨16,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨17,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨18,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨19,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨20,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨21,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨22,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨23,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨24,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨25,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨26,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨27,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨28,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨29,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨30,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨31,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨32,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨33,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨34,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨35,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨36,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨37,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨38,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨39,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨40,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨41,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨42,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨43,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨44,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨45,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨46,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨47,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨48,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨49,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨50,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨51,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12913) (by norm_num)
        (q := 1 - (cell12913 ⟨52,by decide⟩).lower)
        (by norm_num [cell12913]) (by norm_num [cell12913])
      exact ⟨E.1,E.2.trans (by norm_num [cell12913])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12913

/-! Source-cell containment and simple scalar guards at 12913. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12913)
open BstLean.Part268 (cell12913)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12913 ⟨10,by decide⟩).lower ∧ (cell12913 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12913 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12913 ⟨11,by decide⟩).lower ∧ (cell12913 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12913 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12913 ⟨12,by decide⟩).lower ∧ (cell12913 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12913 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12913 ⟨13,by decide⟩).lower ∧ (cell12913 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12913 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12913 ⟨14,by decide⟩).lower ∧ (cell12913 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12913 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12913 ⟨15,by decide⟩).lower ∧ (cell12913 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12913 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12913 ⟨16,by decide⟩).lower ∧ (cell12913 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12913 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12913 ⟨17,by decide⟩).lower ∧ (cell12913 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12913 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12913 ⟨18,by decide⟩).lower ∧ (cell12913 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12913 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12913 ⟨19,by decide⟩).lower ∧ (cell12913 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12913 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12913 ⟨20,by decide⟩).lower ∧ (cell12913 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12913 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12913 ⟨21,by decide⟩).lower ∧ (cell12913 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12913 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12913 ⟨22,by decide⟩).lower ∧ (cell12913 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12913 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12913 ⟨23,by decide⟩).lower ∧ (cell12913 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12913 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12913 ⟨24,by decide⟩).lower ∧ (cell12913 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12913 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12913 ⟨25,by decide⟩).lower ∧ (cell12913 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12913 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12913 ⟨26,by decide⟩).lower ∧ (cell12913 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12913 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12913 ⟨27,by decide⟩).lower ∧ (cell12913 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12913 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12913 ⟨28,by decide⟩).lower ∧ (cell12913 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12913 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12913 ⟨29,by decide⟩).lower ∧ (cell12913 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12913 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12913 ⟨30,by decide⟩).lower ∧ (cell12913 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12913 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12913 ⟨31,by decide⟩).lower ∧ (cell12913 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12913 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12913 ⟨32,by decide⟩).lower ∧ (cell12913 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12913 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12913 ⟨33,by decide⟩).lower ∧ (cell12913 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12913 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12913 ⟨34,by decide⟩).lower ∧ (cell12913 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12913 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12913 ⟨35,by decide⟩).lower ∧ (cell12913 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12913 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12913 ⟨36,by decide⟩).lower ∧ (cell12913 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12913 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12913 ⟨37,by decide⟩).lower ∧ (cell12913 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12913 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12913 ⟨38,by decide⟩).lower ∧ (cell12913 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12913 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12913 ⟨39,by decide⟩).lower ∧ (cell12913 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12913 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12913 ⟨40,by decide⟩).lower ∧ (cell12913 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12913 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12913 ⟨41,by decide⟩).lower ∧ (cell12913 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12913 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12913 ⟨42,by decide⟩).lower ∧ (cell12913 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12913 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12913 ⟨43,by decide⟩).lower ∧ (cell12913 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12913 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12913 ⟨44,by decide⟩).lower ∧ (cell12913 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12913 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12913 ⟨45,by decide⟩).lower ∧ (cell12913 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12913 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12913 ⟨46,by decide⟩).lower ∧ (cell12913 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12913 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12913 ⟨47,by decide⟩).lower ∧ (cell12913 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12913 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12913 ⟨48,by decide⟩).lower ∧ (cell12913 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12913 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12913 ⟨49,by decide⟩).lower ∧ (cell12913 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12913 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12913 ⟨50,by decide⟩).lower ∧ (cell12913 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12913 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12913 ⟨51,by decide⟩).lower ∧ (cell12913 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12913 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12913 ⟨52,by decide⟩).lower ∧ (cell12913 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12913 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12913 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12913 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12913,cell12913,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12913 i).lower ∧
    (cell12913 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12913 i).upper ≤ (0.532 : ℝ) ∧
    (cell12913 i).centre ≤ (0.1 : ℝ) ∧ (cell12913 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12913 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12913 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12913

/-! The local source numeric instances at 12913 have no network premises. -/
namespace BstLean.Part269.N12913
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12913)
open BstLean.Part268 (cell12913)

noncomputable def sourceNumerics12913 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12913 (cell12913 i)
      scalarRow12913.M scalarRow12913.H scalarRow12913.xi := by
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
    energy_allowance := scalarRow12913.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12913]
    centre_nonneg := (scalarRow12913.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12913])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12913
/-! Actual 12914 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12914 ≤ (1.035508682598 : ℝ) := by
  have hr : (113.639781766773 : ℝ) ≤ √(12914 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.639781766773 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12914 12914 (11 / 1000) ≤
    (0.008411552305 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12914) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.639781766773 : ℝ) ≤ √(12914 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12914)
  have hdiv : K / √(12914 : ℝ) ≤ K / 113.639781766773 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.639781766773 ≤ (0.008411552305 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12914.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12914 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12914 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12914 := gPlus_lower 12914
end BstLean.Part269.N12914

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12914
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035508682597 : ℝ) ≤ wn 12914 := by
  have hn : √(12914 : ℝ) ≤ 113.639781766774 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12914 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.639781766774 ≤ 2 / √(12914 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247635038 : ℝ) ≤ rhoBar 12914 BstLean.Part154.csC ∧
    rhoBar 12914 BstLean.Part154.csC ≤ 0.000247635422 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035508682597 : ℝ) / (1.295212 * 12914) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035508682598 : ℝ) / (1.29521 * 12914) := by gcongr
      _ ≤ (0.000247635422 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12914 BstLean.Part154.csC) ≤ 0.000990603012 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12914 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) ≤ 0.000189145458 ∧
    cc1 (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) ≤ 0.000120354541 ∧
    cc2 (rhoBar 12914 BstLean.Part154.csC) ≤ 0.000069866770 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12914 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12914 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12914 BstLean.Part154.csC * nuR (rhoBar 12914 BstLean.Part154.csC)) ≤ 0.000495286175 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247635422 : ℝ) * 0.000990603012 := by gcongr
      _ ≤ (0.000495286175 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12914 BstLean.Part154.csC) * nuR (rhoBar 12914 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990603012 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12914 BstLean.Part154.csC) * rhoBar 12914 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247635422 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247635422 / 2 + 0.399 * 0.000990603012 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189145458 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495286175 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120354541 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247635422 / 1.414213562 := by gcongr
      _ ≤ (0.000069866770 : ℝ) := by norm_num

end BstLean.Part269.N12914

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12914
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) ≤ 1.54500E-7 := by
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12914 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12914 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12914 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189145458 : ℝ) ^ 2 + 0.000120354541 ^ 2 + 3 * 0.000069866770 ^ 2 +
        2 * 0.797885 * 0.000189145458 * 0.000120354541 + 2 * 0.000189145458 * 0.000069866770 +
        4 * 0.797885 * 0.000120354541 * 0.000069866770 := by gcongr
    _ ≤ (1.54500E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12914 BstLean.Part154.csC Θ ≤ 0.002584223828 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12914 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12914 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12914 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035508682598 * 1.54500E-7 / (0.000247635038 : ℝ) := by gcongr
    _ ≤ 0.002584223828 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12914 BstLean.Part154.csC Θ ≤ 0.002866494716 + 0.000652990280 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12914 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12914 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035508682598 : ℝ) * ((2 * Θ * 0.000247635422 +
        (6863 / 10000) * 0.000247635422 * 12914 * 0.000990603012) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002866494716 + 0.000652990280 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12914 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12914 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12914 0.011 Θ ∧ gammaRatio 12914 0.011 Θ ≤ 0.000085130655 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12914 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035508682598 : ℝ) * 0.525 / ((1 - 0.011) * 12914) := by gcongr
      _ ≤ (0.000085130655 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12914 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12914 0.011 Θ) :=
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
    badAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12914 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12914 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12914 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12914 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12914 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12914 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12914 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12914 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12914 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12914 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035508682598 : ℝ) * 12914 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003330165733 + 0.003237214108 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12914

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12914
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12914 BstLean.Part154.csC) (piBar (rhoBar 12914 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12914 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12914 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12914 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12914 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12914 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12914 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12914 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12914 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12914 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12914 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052042937392 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12914) ≤ 0.010508974609 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12914 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035508682598)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010508974609 + 2 * 0.737676 / 12914) := by gcongr
    _ ≤ (0.052042937392 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12914 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12914

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12914
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513085635 : ℝ) ≤ plow 12914 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12914) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536303140)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356717510) : eMP 12914 0.011 xi bn ≤ 0.001168292802 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12914 : ℝ) * (1 - 0.011))) ≤ 0.000577685064 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356717510 / (12914 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577685064 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577685064 : ℝ) + 3.141593 * 0.052536303140 / (12914 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168292802 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536303140)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356717510) : PiBarMP 12914 12 0.011 xi bn ≤ 0.159896096262 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12914 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036833646440 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.013034646451 : ℝ) ≤ √((12914 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.639781766773 : ℝ) ≤ √(12914 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12914) ≤ 0.122601504915 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036833646440 + 0.052536303140 * 1.772454 / (2 * (113.013034646451 : ℝ))) * (1 + 0.001168292802) +
        8 / (12914 * 113.639781766773) + 0.122601504915 := by gcongr
    _ ≤ (0.159896096262 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536303140)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356717510) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281250928396) :
    parallelOracle 12914 0.011 xi bn cd ≤ 0.160870033961 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12914 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12914 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513085635 : ℝ) ≤ plow 12914 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.639781766773 : ℝ) ≤ √(12914 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281250928396 : ℝ) / (2 * 0.560513085635 * 113.639781766773)) * 0.159896096262 +
        0.281250928396 ^ 2 / (2 * 0.560513085635 * 113.639781766773) := by gcongr
    _ ≤ (0.160870033961 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052536303140) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356717510)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281250928396) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12914 12914 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513085635 : ℝ) ≤ plow 12914 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.639781766773 : ℝ) ≤ √(12914 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12914 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12914 Θ 1.22 ≤ 0.011669333392 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.639781766773 := by gcongr <;> linarith
      _ ≤ (0.011669333392 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12914 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12914 12914 0.011 ≤ 0.008411552305 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12914 12914 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12914 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12914 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12914 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12914 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160870033961 + 0.011669333392 + (0.008411552305 : ℝ) *
        (1 + 2 * (0.281250928396 + 0.011669333392) / (0.560513085635 * 113.639781766773))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12914]

end BstLean.Part269.N12914

/-! The original eight local profiles supply actual 12914 moment certificates. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12914 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052536303140 ∧
    0 ≤ bN 12914 BstLean.Part154.csC (groupTheta g) ∧ bN 12914 BstLean.Part154.csC (groupTheta g) ≤ 0.001356717510 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12914 12914 0.011
      (momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12914 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12914 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12914 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229207991004 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12914 0.011
      (momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12914 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12914
/-! The actual computed-centre upper energy formula at 12914. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12914

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12914)
open BstLean.Part268 (cell12914)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084889312988
  | 2 => 0.085821527361
  | 3 => 0.086750427632
  | 4 => 0.087677091460
  | 5 => 0.088602832635
  | 6 => 0.089529237441
  | 7 => 0.090458204694
  | 8 => 0.091391989527
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12914 12914 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12914 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12914

/-! Actual upper energy certificates on all 43 source endpoints at 12914. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12914)
open BstLean.Part268 (cell12914)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12914 (gMinus 12914) (1 - (cell12914 i).lower) ≤ 1 ∧
    energyUpper 12914 (gMinus 12914) (BstLean.Part211.gPlus 12914)
      (finiteEnergy 12914 12914 0.011) (1 - (cell12914 i).lower) ≤
      (cell12914 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨10,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨11,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨12,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨13,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨14,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨15,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨16,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨17,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨18,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨19,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨20,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨21,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨22,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨23,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨24,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨25,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨26,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨27,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨28,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨29,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨30,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨31,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨32,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨33,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨34,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨35,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨36,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨37,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨38,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨39,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨40,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨41,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨42,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨43,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨44,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨45,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨46,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨47,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨48,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨49,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨50,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨51,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12914) (by norm_num)
        (q := 1 - (cell12914 ⟨52,by decide⟩).lower)
        (by norm_num [cell12914]) (by norm_num [cell12914])
      exact ⟨E.1,E.2.trans (by norm_num [cell12914])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12914

/-! Source-cell containment and simple scalar guards at 12914. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12914)
open BstLean.Part268 (cell12914)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12914 ⟨10,by decide⟩).lower ∧ (cell12914 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12914 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12914 ⟨11,by decide⟩).lower ∧ (cell12914 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12914 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12914 ⟨12,by decide⟩).lower ∧ (cell12914 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12914 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12914 ⟨13,by decide⟩).lower ∧ (cell12914 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12914 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12914 ⟨14,by decide⟩).lower ∧ (cell12914 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12914 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12914 ⟨15,by decide⟩).lower ∧ (cell12914 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12914 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12914 ⟨16,by decide⟩).lower ∧ (cell12914 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12914 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12914 ⟨17,by decide⟩).lower ∧ (cell12914 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12914 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12914 ⟨18,by decide⟩).lower ∧ (cell12914 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12914 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12914 ⟨19,by decide⟩).lower ∧ (cell12914 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12914 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12914 ⟨20,by decide⟩).lower ∧ (cell12914 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12914 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12914 ⟨21,by decide⟩).lower ∧ (cell12914 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12914 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12914 ⟨22,by decide⟩).lower ∧ (cell12914 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12914 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12914 ⟨23,by decide⟩).lower ∧ (cell12914 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12914 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12914 ⟨24,by decide⟩).lower ∧ (cell12914 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12914 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12914 ⟨25,by decide⟩).lower ∧ (cell12914 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12914 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12914 ⟨26,by decide⟩).lower ∧ (cell12914 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12914 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12914 ⟨27,by decide⟩).lower ∧ (cell12914 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12914 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12914 ⟨28,by decide⟩).lower ∧ (cell12914 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12914 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12914 ⟨29,by decide⟩).lower ∧ (cell12914 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12914 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12914 ⟨30,by decide⟩).lower ∧ (cell12914 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12914 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12914 ⟨31,by decide⟩).lower ∧ (cell12914 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12914 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12914 ⟨32,by decide⟩).lower ∧ (cell12914 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12914 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12914 ⟨33,by decide⟩).lower ∧ (cell12914 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12914 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12914 ⟨34,by decide⟩).lower ∧ (cell12914 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12914 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12914 ⟨35,by decide⟩).lower ∧ (cell12914 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12914 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12914 ⟨36,by decide⟩).lower ∧ (cell12914 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12914 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12914 ⟨37,by decide⟩).lower ∧ (cell12914 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12914 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12914 ⟨38,by decide⟩).lower ∧ (cell12914 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12914 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12914 ⟨39,by decide⟩).lower ∧ (cell12914 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12914 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12914 ⟨40,by decide⟩).lower ∧ (cell12914 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12914 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12914 ⟨41,by decide⟩).lower ∧ (cell12914 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12914 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12914 ⟨42,by decide⟩).lower ∧ (cell12914 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12914 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12914 ⟨43,by decide⟩).lower ∧ (cell12914 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12914 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12914 ⟨44,by decide⟩).lower ∧ (cell12914 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12914 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12914 ⟨45,by decide⟩).lower ∧ (cell12914 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12914 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12914 ⟨46,by decide⟩).lower ∧ (cell12914 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12914 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12914 ⟨47,by decide⟩).lower ∧ (cell12914 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12914 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12914 ⟨48,by decide⟩).lower ∧ (cell12914 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12914 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12914 ⟨49,by decide⟩).lower ∧ (cell12914 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12914 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12914 ⟨50,by decide⟩).lower ∧ (cell12914 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12914 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12914 ⟨51,by decide⟩).lower ∧ (cell12914 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12914 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12914 ⟨52,by decide⟩).lower ∧ (cell12914 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12914 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12914 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12914 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12914,cell12914,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12914 i).lower ∧
    (cell12914 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12914 i).upper ≤ (0.532 : ℝ) ∧
    (cell12914 i).centre ≤ (0.1 : ℝ) ∧ (cell12914 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12914 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12914 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12914

/-! The local source numeric instances at 12914 have no network premises. -/
namespace BstLean.Part269.N12914
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12914)
open BstLean.Part268 (cell12914)

noncomputable def sourceNumerics12914 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12914 (cell12914 i)
      scalarRow12914.M scalarRow12914.H scalarRow12914.xi := by
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
    energy_allowance := scalarRow12914.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12914]
    centre_nonneg := (scalarRow12914.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12914])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12914
/-! Actual 12915 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12915 ≤ (1.035507295873 : ℝ) := by
  have hr : (113.644181549254 : ℝ) ≤ √(12915 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.644181549254 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12915 12915 (11 / 1000) ≤
    (0.008411226645 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12915) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.644181549254 : ℝ) ≤ √(12915 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12915)
  have hdiv : K / √(12915 : ℝ) ≤ K / 113.644181549254 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.644181549254 ≤ (0.008411226645 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12915.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12915 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12915 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12915 := gPlus_lower 12915
end BstLean.Part269.N12915

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12915
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035507295872 : ℝ) ≤ wn 12915 := by
  have hn : √(12915 : ℝ) ≤ 113.644181549255 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12915 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.644181549255 ≤ 2 / √(12915 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247615532 : ℝ) ≤ rhoBar 12915 BstLean.Part154.csC ∧
    rhoBar 12915 BstLean.Part154.csC ≤ 0.000247615916 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035507295872 : ℝ) / (1.295212 * 12915) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035507295873 : ℝ) / (1.29521 * 12915) := by gcongr
      _ ≤ (0.000247615916 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12915 BstLean.Part154.csC) ≤ 0.000990524978 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12915 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) ≤ 0.000189130558 ∧
    cc1 (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) ≤ 0.000120345061 ∧
    cc2 (rhoBar 12915 BstLean.Part154.csC) ≤ 0.000069861267 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12915 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12915 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12915 BstLean.Part154.csC * nuR (rhoBar 12915 BstLean.Part154.csC)) ≤ 0.000495247161 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247615916 : ℝ) * 0.000990524978 := by gcongr
      _ ≤ (0.000495247161 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12915 BstLean.Part154.csC) * nuR (rhoBar 12915 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990524978 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12915 BstLean.Part154.csC) * rhoBar 12915 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247615916 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247615916 / 2 + 0.399 * 0.000990524978 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189130558 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495247161 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120345061 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247615916 / 1.414213562 := by gcongr
      _ ≤ (0.000069861267 : ℝ) := by norm_num

end BstLean.Part269.N12915

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12915
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) ≤ 1.54475E-7 := by
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12915 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12915 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12915 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189130558 : ℝ) ^ 2 + 0.000120345061 ^ 2 + 3 * 0.000069861267 ^ 2 +
        2 * 0.797885 * 0.000189130558 * 0.000120345061 + 2 * 0.000189130558 * 0.000069861267 +
        4 * 0.797885 * 0.000120345061 * 0.000069861267 := by gcongr
    _ ≤ (1.54475E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12915 BstLean.Part154.csC Θ ≤ 0.002584005749 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12915 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12915 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12915 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035507295873 * 1.54475E-7 / (0.000247615532 : ℝ) := by gcongr
    _ ≤ 0.002584005749 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12915 BstLean.Part154.csC Θ ≤ 0.002866261232 + 0.000652937970 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12915 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12915 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035507295873 : ℝ) * ((2 * Θ * 0.000247615916 +
        (6863 / 10000) * 0.000247615916 * 12915 * 0.000990524978) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002866261232 + 0.000652937970 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12915 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12915 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12915 0.011 Θ ∧ gammaRatio 12915 0.011 Θ ≤ 0.000085123949 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12915 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035507295873 : ℝ) * 0.525 / ((1 - 0.011) * 12915) := by gcongr
      _ ≤ (0.000085123949 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12915 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12915 0.011 Θ) :=
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
    badAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12915 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12915 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12915 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12915 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12915 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12915 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12915 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12915 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12915 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12915 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035507295873 : ℝ) * 12915 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003329932249 + 0.003236943719 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12915

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12915
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12915 BstLean.Part154.csC) (piBar (rhoBar 12915 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12915 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12915 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12915 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12915 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12915 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12915 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12915 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12915 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12915 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12915 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052040900858 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12915) ≤ 0.010508567749 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12915 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035507295873)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010508567749 + 2 * 0.737676 / 12915) := by gcongr
    _ ≤ (0.052040900858 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12915 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12915

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12915
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513129368 : ℝ) ≤ plow 12915 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12915) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535927702)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356603019) : eMP 12915 0.011 xi bn ≤ 0.001168198229 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12915 : ℝ) * (1 - 0.011))) ≤ 0.000577638324 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356603019 / (12915 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577638324 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577638324 : ℝ) + 3.141593 * 0.052535927702 / (12915 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168198229 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535927702)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356603019) : PiBarMP 12915 12 0.011 xi bn ≤ 0.159889770610 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12915 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036832092244 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.017410163213 : ℝ) ≤ √((12915 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.644181549254 : ℝ) ≤ √(12915 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12915) ≤ 0.122596758346 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036832092244 + 0.052535927702 * 1.772454 / (2 * (113.017410163213 : ℝ))) * (1 + 0.001168198229) +
        8 / (12915 * 113.644181549254) + 0.122596758346 := by gcongr
    _ ≤ (0.159889770610 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535927702)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356603019) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281248072871) :
    parallelOracle 12915 0.011 xi bn cd ≤ 0.160863640370 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12915 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12915 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513129368 : ℝ) ≤ plow 12915 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.644181549254 : ℝ) ≤ √(12915 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281248072871 : ℝ) / (2 * 0.560513129368 * 113.644181549254)) * 0.159889770610 +
        0.281248072871 ^ 2 / (2 * 0.560513129368 * 113.644181549254) := by gcongr
    _ ≤ (0.160863640370 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535927702) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356603019)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281248072871) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12915 12915 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513129368 : ℝ) ≤ plow 12915 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.644181549254 : ℝ) ≤ √(12915 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12915 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12915 Θ 1.22 ≤ 0.011668881609 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.644181549254 := by gcongr <;> linarith
      _ ≤ (0.011668881609 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12915 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12915 12915 0.011 ≤ 0.008411226645 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12915 12915 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12915 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12915 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12915 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12915 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160863640370 + 0.011668881609 + (0.008411226645 : ℝ) *
        (1 + 2 * (0.281248072871 + 0.011668881609) / (0.560513129368 * 113.644181549254))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12915]

end BstLean.Part269.N12915

/-! The original eight local profiles supply actual 12915 moment certificates. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12915 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052535927702 ∧
    0 ≤ bN 12915 BstLean.Part154.csC (groupTheta g) ∧ bN 12915 BstLean.Part154.csC (groupTheta g) ≤ 0.001356603019 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12915 12915 0.011
      (momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12915 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12915 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12915 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229207172013 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12915 0.011
      (momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12915 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12915
/-! The actual computed-centre upper energy formula at 12915. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12915

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12915)
open BstLean.Part268 (cell12915)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084886606113
  | 2 => 0.085818775243
  | 3 => 0.086747624415
  | 4 => 0.087674229892
  | 5 => 0.088599903813
  | 6 => 0.089526230522
  | 7 => 0.090455106575
  | 8 => 0.091388784480
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12915 12915 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12915 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12915

/-! Actual upper energy certificates on all 43 source endpoints at 12915. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12915)
open BstLean.Part268 (cell12915)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12915 (gMinus 12915) (1 - (cell12915 i).lower) ≤ 1 ∧
    energyUpper 12915 (gMinus 12915) (BstLean.Part211.gPlus 12915)
      (finiteEnergy 12915 12915 0.011) (1 - (cell12915 i).lower) ≤
      (cell12915 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨10,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨11,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨12,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨13,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨14,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨15,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨16,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨17,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨18,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨19,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨20,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨21,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨22,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨23,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨24,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨25,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨26,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨27,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨28,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨29,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨30,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨31,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨32,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨33,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨34,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨35,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨36,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨37,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨38,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨39,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨40,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨41,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨42,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨43,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨44,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨45,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨46,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨47,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨48,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨49,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨50,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨51,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12915) (by norm_num)
        (q := 1 - (cell12915 ⟨52,by decide⟩).lower)
        (by norm_num [cell12915]) (by norm_num [cell12915])
      exact ⟨E.1,E.2.trans (by norm_num [cell12915])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12915

/-! Source-cell containment and simple scalar guards at 12915. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12915)
open BstLean.Part268 (cell12915)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12915 ⟨10,by decide⟩).lower ∧ (cell12915 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12915 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12915 ⟨11,by decide⟩).lower ∧ (cell12915 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12915 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12915 ⟨12,by decide⟩).lower ∧ (cell12915 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12915 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12915 ⟨13,by decide⟩).lower ∧ (cell12915 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12915 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12915 ⟨14,by decide⟩).lower ∧ (cell12915 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12915 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12915 ⟨15,by decide⟩).lower ∧ (cell12915 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12915 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12915 ⟨16,by decide⟩).lower ∧ (cell12915 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12915 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12915 ⟨17,by decide⟩).lower ∧ (cell12915 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12915 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12915 ⟨18,by decide⟩).lower ∧ (cell12915 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12915 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12915 ⟨19,by decide⟩).lower ∧ (cell12915 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12915 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12915 ⟨20,by decide⟩).lower ∧ (cell12915 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12915 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12915 ⟨21,by decide⟩).lower ∧ (cell12915 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12915 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12915 ⟨22,by decide⟩).lower ∧ (cell12915 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12915 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12915 ⟨23,by decide⟩).lower ∧ (cell12915 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12915 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12915 ⟨24,by decide⟩).lower ∧ (cell12915 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12915 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12915 ⟨25,by decide⟩).lower ∧ (cell12915 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12915 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12915 ⟨26,by decide⟩).lower ∧ (cell12915 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12915 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12915 ⟨27,by decide⟩).lower ∧ (cell12915 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12915 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12915 ⟨28,by decide⟩).lower ∧ (cell12915 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12915 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12915 ⟨29,by decide⟩).lower ∧ (cell12915 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12915 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12915 ⟨30,by decide⟩).lower ∧ (cell12915 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12915 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12915 ⟨31,by decide⟩).lower ∧ (cell12915 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12915 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12915 ⟨32,by decide⟩).lower ∧ (cell12915 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12915 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12915 ⟨33,by decide⟩).lower ∧ (cell12915 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12915 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12915 ⟨34,by decide⟩).lower ∧ (cell12915 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12915 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12915 ⟨35,by decide⟩).lower ∧ (cell12915 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12915 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12915 ⟨36,by decide⟩).lower ∧ (cell12915 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12915 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12915 ⟨37,by decide⟩).lower ∧ (cell12915 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12915 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12915 ⟨38,by decide⟩).lower ∧ (cell12915 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12915 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12915 ⟨39,by decide⟩).lower ∧ (cell12915 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12915 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12915 ⟨40,by decide⟩).lower ∧ (cell12915 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12915 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12915 ⟨41,by decide⟩).lower ∧ (cell12915 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12915 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12915 ⟨42,by decide⟩).lower ∧ (cell12915 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12915 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12915 ⟨43,by decide⟩).lower ∧ (cell12915 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12915 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12915 ⟨44,by decide⟩).lower ∧ (cell12915 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12915 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12915 ⟨45,by decide⟩).lower ∧ (cell12915 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12915 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12915 ⟨46,by decide⟩).lower ∧ (cell12915 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12915 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12915 ⟨47,by decide⟩).lower ∧ (cell12915 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12915 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12915 ⟨48,by decide⟩).lower ∧ (cell12915 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12915 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12915 ⟨49,by decide⟩).lower ∧ (cell12915 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12915 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12915 ⟨50,by decide⟩).lower ∧ (cell12915 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12915 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12915 ⟨51,by decide⟩).lower ∧ (cell12915 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12915 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12915 ⟨52,by decide⟩).lower ∧ (cell12915 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12915 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12915 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12915 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12915,cell12915,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12915 i).lower ∧
    (cell12915 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12915 i).upper ≤ (0.532 : ℝ) ∧
    (cell12915 i).centre ≤ (0.1 : ℝ) ∧ (cell12915 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12915 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12915 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12915

/-! The local source numeric instances at 12915 have no network premises. -/
namespace BstLean.Part269.N12915
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12915)
open BstLean.Part268 (cell12915)

noncomputable def sourceNumerics12915 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12915 (cell12915 i)
      scalarRow12915.M scalarRow12915.H scalarRow12915.xi := by
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
    energy_allowance := scalarRow12915.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12915]
    centre_nonneg := (scalarRow12915.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12915])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12915
/-! Actual 12916 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12916 ≤ (1.035505909310 : ℝ) := by
  have hr : (113.648581161402 : ℝ) ≤ √(12916 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.648581161402 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12916 12916 (11 / 1000) ≤
    (0.008410901024 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12916) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.648581161402 : ℝ) ≤ √(12916 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12916)
  have hdiv : K / √(12916 : ℝ) ≤ K / 113.648581161402 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.648581161402 ≤ (0.008410901024 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12916.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12916 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12916 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12916 := gPlus_lower 12916
end BstLean.Part269.N12916

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12916
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035505909309 : ℝ) ≤ wn 12916 := by
  have hn : √(12916 : ℝ) ≤ 113.648581161403 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12916 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.648581161403 ≤ 2 / √(12916 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247596030 : ℝ) ≤ rhoBar 12916 BstLean.Part154.csC ∧
    rhoBar 12916 BstLean.Part154.csC ≤ 0.000247596413 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035505909309 : ℝ) / (1.295212 * 12916) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035505909310 : ℝ) / (1.29521 * 12916) := by gcongr
      _ ≤ (0.000247596413 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12916 BstLean.Part154.csC) ≤ 0.000990446956 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12916 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) ≤ 0.000189115661 ∧
    cc1 (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) ≤ 0.000120335581 ∧
    cc2 (rhoBar 12916 BstLean.Part154.csC) ≤ 0.000069855764 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12916 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12916 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12916 BstLean.Part154.csC * nuR (rhoBar 12916 BstLean.Part154.csC)) ≤ 0.000495208152 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247596413 : ℝ) * 0.000990446956 := by gcongr
      _ ≤ (0.000495208152 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12916 BstLean.Part154.csC) * nuR (rhoBar 12916 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990446956 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12916 BstLean.Part154.csC) * rhoBar 12916 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247596413 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247596413 / 2 + 0.399 * 0.000990446956 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189115661 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495208152 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120335581 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247596413 / 1.414213562 := by gcongr
      _ ≤ (0.000069855764 : ℝ) := by norm_num

end BstLean.Part269.N12916

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12916
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) ≤ 1.54451E-7 := by
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12916 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12916 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12916 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189115661 : ℝ) ^ 2 + 0.000120335581 ^ 2 + 3 * 0.000069855764 ^ 2 +
        2 * 0.797885 * 0.000189115661 * 0.000120335581 + 2 * 0.000189115661 * 0.000069855764 +
        4 * 0.797885 * 0.000120335581 * 0.000069855764 := by gcongr
    _ ≤ (1.54451E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12916 BstLean.Part154.csC Θ ≤ 0.002583804324 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12916 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12916 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12916 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035505909310 * 1.54451E-7 / (0.000247596030 : ℝ) := by gcongr
    _ ≤ 0.002583804324 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12916 BstLean.Part154.csC Θ ≤ 0.002866027783 + 0.000652885668 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12916 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12916 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035505909310 : ℝ) * ((2 * Θ * 0.000247596413 +
        (6863 / 10000) * 0.000247596413 * 12916 * 0.000990446956) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002866027783 + 0.000652885668 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12916 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12916 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12916 0.011 Θ ∧ gammaRatio 12916 0.011 Θ ≤ 0.000085117244 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12916 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035505909310 : ℝ) * 0.525 / ((1 - 0.011) * 12916) := by gcongr
      _ ≤ (0.000085117244 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12916 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12916 0.011 Θ) :=
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
    badAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12916 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12916 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12916 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12916 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12916 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12916 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12916 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12916 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12916 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12916 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035505909310 : ℝ) * 12916 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003329698800 + 0.003236689992 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12916

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12916
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12916 BstLean.Part154.csC) (piBar (rhoBar 12916 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12916 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12916 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12916 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12916 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12916 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12916 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12916 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12916 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12916 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12916 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052038864565 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12916) ≤ 0.010508160937 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12916 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035505909310)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010508160937 + 2 * 0.737676 / 12916) := by gcongr
    _ ≤ (0.052038864565 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12916 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12916

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12916
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513173095 : ℝ) ≤ plow 12916 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12916) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535561046)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356497271) : eMP 12916 0.011 xi bn ≤ 0.001168107388 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12916 : ℝ) * (1 - 0.011))) ≤ 0.000577593449 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356497271 / (12916 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577593449 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577593449 : ℝ) + 3.141593 * 0.052535561046 / (12916 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168107388 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535561046)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356497271) : PiBarMP 12916 12 0.011 xi bn ≤ 0.159883564484 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12916 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036830656674 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.021785510581 : ℝ) ≤ √((12916 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.648581161402 : ℝ) ≤ √(12916 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12916) ≤ 0.122592012328 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036830656674 + 0.052535561046 * 1.772454 / (2 * (113.021785510581 : ℝ))) * (1 + 0.001168107388) +
        8 / (12916 * 113.648581161402) + 0.122592012328 := by gcongr
    _ ≤ (0.159883564484 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535561046)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356497271) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281245236741) :
    parallelOracle 12916 0.011 xi bn cd ≤ 0.160857366686 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12916 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12916 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513173095 : ℝ) ≤ plow 12916 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.648581161402 : ℝ) ≤ √(12916 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281245236741 : ℝ) / (2 * 0.560513173095 * 113.648581161402)) * 0.159883564484 +
        0.281245236741 ^ 2 / (2 * 0.560513173095 * 113.648581161402) := by gcongr
    _ ≤ (0.160857366686 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535561046) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356497271)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281245236741) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12916 12916 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513173095 : ℝ) ≤ plow 12916 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.648581161402 : ℝ) ≤ √(12916 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12916 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12916 Θ 1.22 ≤ 0.011668429878 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.648581161402 := by gcongr <;> linarith
      _ ≤ (0.011668429878 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12916 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12916 12916 0.011 ≤ 0.008410901024 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12916 12916 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12916 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12916 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12916 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12916 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160857366686 + 0.011668429878 + (0.008410901024 : ℝ) *
        (1 + 2 * (0.281245236741 + 0.011668429878) / (0.560513173095 * 113.648581161402))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12916]

end BstLean.Part269.N12916

/-! The original eight local profiles supply actual 12916 moment certificates. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12916 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052535561046 ∧
    0 ≤ bN 12916 BstLean.Part154.csC (groupTheta g) ∧ bN 12916 BstLean.Part154.csC (groupTheta g) ≤ 0.001356497271 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12916 12916 0.011
      (momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12916 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12916 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12916 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229206372176 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12916 0.011
      (momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12916 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12916
/-! The actual computed-centre upper energy formula at 12916. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12916

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12916)
open BstLean.Part268 (cell12916)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084883900116
  | 2 => 0.085816024036
  | 3 => 0.086744822151
  | 4 => 0.087671369328
  | 5 => 0.088596976057
  | 6 => 0.089523224747
  | 7 => 0.090452009692
  | 8 => 0.091385580781
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12916 12916 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12916 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12916

/-! Actual upper energy certificates on all 43 source endpoints at 12916. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12916)
open BstLean.Part268 (cell12916)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12916 (gMinus 12916) (1 - (cell12916 i).lower) ≤ 1 ∧
    energyUpper 12916 (gMinus 12916) (BstLean.Part211.gPlus 12916)
      (finiteEnergy 12916 12916 0.011) (1 - (cell12916 i).lower) ≤
      (cell12916 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨10,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨11,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨12,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨13,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨14,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨15,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨16,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨17,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨18,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨19,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨20,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨21,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨22,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨23,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨24,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨25,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨26,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨27,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨28,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨29,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨30,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨31,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨32,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨33,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨34,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨35,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨36,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨37,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨38,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨39,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨40,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨41,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨42,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨43,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨44,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨45,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨46,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨47,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨48,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨49,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨50,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨51,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12916) (by norm_num)
        (q := 1 - (cell12916 ⟨52,by decide⟩).lower)
        (by norm_num [cell12916]) (by norm_num [cell12916])
      exact ⟨E.1,E.2.trans (by norm_num [cell12916])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12916

/-! Source-cell containment and simple scalar guards at 12916. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12916)
open BstLean.Part268 (cell12916)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12916 ⟨10,by decide⟩).lower ∧ (cell12916 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12916 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12916 ⟨11,by decide⟩).lower ∧ (cell12916 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12916 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12916 ⟨12,by decide⟩).lower ∧ (cell12916 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12916 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12916 ⟨13,by decide⟩).lower ∧ (cell12916 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12916 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12916 ⟨14,by decide⟩).lower ∧ (cell12916 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12916 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12916 ⟨15,by decide⟩).lower ∧ (cell12916 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12916 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12916 ⟨16,by decide⟩).lower ∧ (cell12916 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12916 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12916 ⟨17,by decide⟩).lower ∧ (cell12916 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12916 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12916 ⟨18,by decide⟩).lower ∧ (cell12916 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12916 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12916 ⟨19,by decide⟩).lower ∧ (cell12916 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12916 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12916 ⟨20,by decide⟩).lower ∧ (cell12916 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12916 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12916 ⟨21,by decide⟩).lower ∧ (cell12916 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12916 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12916 ⟨22,by decide⟩).lower ∧ (cell12916 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12916 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12916 ⟨23,by decide⟩).lower ∧ (cell12916 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12916 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12916 ⟨24,by decide⟩).lower ∧ (cell12916 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12916 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12916 ⟨25,by decide⟩).lower ∧ (cell12916 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12916 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12916 ⟨26,by decide⟩).lower ∧ (cell12916 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12916 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12916 ⟨27,by decide⟩).lower ∧ (cell12916 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12916 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12916 ⟨28,by decide⟩).lower ∧ (cell12916 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12916 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12916 ⟨29,by decide⟩).lower ∧ (cell12916 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12916 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12916 ⟨30,by decide⟩).lower ∧ (cell12916 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12916 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12916 ⟨31,by decide⟩).lower ∧ (cell12916 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12916 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12916 ⟨32,by decide⟩).lower ∧ (cell12916 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12916 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12916 ⟨33,by decide⟩).lower ∧ (cell12916 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12916 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12916 ⟨34,by decide⟩).lower ∧ (cell12916 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12916 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12916 ⟨35,by decide⟩).lower ∧ (cell12916 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12916 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12916 ⟨36,by decide⟩).lower ∧ (cell12916 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12916 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12916 ⟨37,by decide⟩).lower ∧ (cell12916 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12916 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12916 ⟨38,by decide⟩).lower ∧ (cell12916 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12916 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12916 ⟨39,by decide⟩).lower ∧ (cell12916 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12916 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12916 ⟨40,by decide⟩).lower ∧ (cell12916 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12916 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12916 ⟨41,by decide⟩).lower ∧ (cell12916 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12916 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12916 ⟨42,by decide⟩).lower ∧ (cell12916 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12916 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12916 ⟨43,by decide⟩).lower ∧ (cell12916 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12916 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12916 ⟨44,by decide⟩).lower ∧ (cell12916 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12916 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12916 ⟨45,by decide⟩).lower ∧ (cell12916 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12916 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12916 ⟨46,by decide⟩).lower ∧ (cell12916 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12916 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12916 ⟨47,by decide⟩).lower ∧ (cell12916 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12916 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12916 ⟨48,by decide⟩).lower ∧ (cell12916 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12916 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12916 ⟨49,by decide⟩).lower ∧ (cell12916 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12916 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12916 ⟨50,by decide⟩).lower ∧ (cell12916 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12916 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12916 ⟨51,by decide⟩).lower ∧ (cell12916 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12916 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12916 ⟨52,by decide⟩).lower ∧ (cell12916 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12916 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12916 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12916 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12916,cell12916,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12916 i).lower ∧
    (cell12916 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12916 i).upper ≤ (0.532 : ℝ) ∧
    (cell12916 i).centre ≤ (0.1 : ℝ) ∧ (cell12916 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12916 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12916 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12916

/-! The local source numeric instances at 12916 have no network premises. -/
namespace BstLean.Part269.N12916
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12916)
open BstLean.Part268 (cell12916)

noncomputable def sourceNumerics12916 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12916 (cell12916 i)
      scalarRow12916.M scalarRow12916.H scalarRow12916.xi := by
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
    energy_allowance := scalarRow12916.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12916]
    centre_nonneg := (scalarRow12916.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12916])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12916
/-! Actual 12917 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12917 ≤ (1.035504522909 : ℝ) := by
  have hr : (113.652980603238 : ℝ) ≤ √(12917 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.652980603238 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12917 12917 (11 / 1000) ≤
    (0.008410575440 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12917) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.652980603238 : ℝ) ≤ √(12917 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12917)
  have hdiv : K / √(12917 : ℝ) ≤ K / 113.652980603238 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.652980603238 ≤ (0.008410575440 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12917.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12917 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12917 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12917 := gPlus_lower 12917
end BstLean.Part269.N12917

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12917
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035504522908 : ℝ) ≤ wn 12917 := by
  have hn : √(12917 : ℝ) ≤ 113.652980603239 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12917 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.652980603239 ≤ 2 / √(12917 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247576530 : ℝ) ≤ rhoBar 12917 BstLean.Part154.csC ∧
    rhoBar 12917 BstLean.Part154.csC ≤ 0.000247576913 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035504522908 : ℝ) / (1.295212 * 12917) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035504522909 : ℝ) / (1.29521 * 12917) := by gcongr
      _ ≤ (0.000247576913 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12917 BstLean.Part154.csC) ≤ 0.000990368947 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12917 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) ≤ 0.000189100766 ∧
    cc1 (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) ≤ 0.000120326104 ∧
    cc2 (rhoBar 12917 BstLean.Part154.csC) ≤ 0.000069850263 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12917 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12917 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12917 BstLean.Part154.csC * nuR (rhoBar 12917 BstLean.Part154.csC)) ≤ 0.000495169150 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247576913 : ℝ) * 0.000990368947 := by gcongr
      _ ≤ (0.000495169150 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12917 BstLean.Part154.csC) * nuR (rhoBar 12917 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990368947 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12917 BstLean.Part154.csC) * rhoBar 12917 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247576913 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247576913 / 2 + 0.399 * 0.000990368947 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189100766 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495169150 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120326104 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247576913 / 1.414213562 := by gcongr
      _ ≤ (0.000069850263 : ℝ) := by norm_num

end BstLean.Part269.N12917

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12917
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) ≤ 1.54427E-7 := by
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12917 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12917 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12917 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189100766 : ℝ) ^ 2 + 0.000120326104 ^ 2 + 3 * 0.000069850263 ^ 2 +
        2 * 0.797885 * 0.000189100766 * 0.000120326104 + 2 * 0.000189100766 * 0.000069850263 +
        4 * 0.797885 * 0.000120326104 * 0.000069850263 := by gcongr
    _ ≤ (1.54427E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12917 BstLean.Part154.csC Θ ≤ 0.002583602848 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12917 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12917 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12917 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035504522909 * 1.54427E-7 / (0.000247576530 : ℝ) := by gcongr
    _ ≤ 0.002583602848 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12917 BstLean.Part154.csC Θ ≤ 0.002865794374 + 0.000652833375 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12917 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12917 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035504522909 : ℝ) * ((2 * Θ * 0.000247576913 +
        (6863 / 10000) * 0.000247576913 * 12917 * 0.000990368947) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002865794374 + 0.000652833375 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12917 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12917 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12917 0.011 Θ ∧ gammaRatio 12917 0.011 Θ ≤ 0.000085110541 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12917 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035504522909 : ℝ) * 0.525 / ((1 - 0.011) * 12917) := by gcongr
      _ ≤ (0.000085110541 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12917 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12917 0.011 Θ) :=
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
    badAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12917 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12917 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12917 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12917 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12917 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12917 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12917 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12917 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12917 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12917 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035504522909 : ℝ) * 12917 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003329465391 + 0.003236436223 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12917

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12917
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12917 BstLean.Part154.csC) (piBar (rhoBar 12917 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12917 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12917 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12917 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12917 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12917 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12917 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12917 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12917 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12917 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12917 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052036828509 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12917) ≤ 0.010507754172 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12917 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035504522909)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010507754172 + 2 * 0.737676 / 12917) := by gcongr
    _ ≤ (0.052036828509 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12917 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12917

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12917
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513216815 : ℝ) ≤ plow 12917 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12917) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535194409)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356391496) : eMP 12917 0.011 xi bn ≤ 0.001168016544 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12917 : ℝ) * (1 - 0.011))) ≤ 0.000577548572 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356391496 / (12917 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577548572 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577548572 : ℝ) + 3.141593 * 0.052535194409 / (12917 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168016544 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535194409)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356391496) : PiBarMP 12917 12 0.011 xi bn ≤ 0.159877358489 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12917 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036829220682 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.026160688576 : ℝ) ≤ √((12917 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.652980603238 : ℝ) ≤ √(12917 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12917) ≤ 0.122587266861 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036829220682 + 0.052535194409 * 1.772454 / (2 * (113.026160688576 : ℝ))) * (1 + 0.001168016544) +
        8 / (12917 * 113.652980603238) + 0.122587266861 := by gcongr
    _ ≤ (0.159877358489 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535194409)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356391496) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281242400887) :
    parallelOracle 12917 0.011 xi bn cd ≤ 0.160851093142 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12917 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12917 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513216815 : ℝ) ≤ plow 12917 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.652980603238 : ℝ) ≤ √(12917 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281242400887 : ℝ) / (2 * 0.560513216815 * 113.652980603238)) * 0.159877358489 +
        0.281242400887 ^ 2 / (2 * 0.560513216815 * 113.652980603238) := by gcongr
    _ ≤ (0.160851093142 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052535194409) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356391496)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281242400887) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12917 12917 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513216815 : ℝ) ≤ plow 12917 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.652980603238 : ℝ) ≤ √(12917 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12917 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12917 Θ 1.22 ≤ 0.011667978200 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.652980603238 := by gcongr <;> linarith
      _ ≤ (0.011667978200 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12917 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12917 12917 0.011 ≤ 0.008410575440 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12917 12917 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12917 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12917 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12917 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12917 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160851093142 + 0.011667978200 + (0.008410575440 : ℝ) *
        (1 + 2 * (0.281242400887 + 0.011667978200) / (0.560513216815 * 113.652980603238))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12917]

end BstLean.Part269.N12917

/-! The original eight local profiles supply actual 12917 moment certificates. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12917 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052535194409 ∧
    0 ≤ bN 12917 BstLean.Part154.csC (groupTheta g) ∧ bN 12917 BstLean.Part154.csC (groupTheta g) ≤ 0.001356391496 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12917 12917 0.011
      (momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12917 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12917 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12917 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229205572378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12917 0.011
      (momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12917 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12917
/-! The actual computed-centre upper energy formula at 12917. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12917

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12917)
open BstLean.Part268 (cell12917)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084881194996
  | 2 => 0.085813273740
  | 3 => 0.086742020839
  | 4 => 0.087668509768
  | 5 => 0.088594049368
  | 6 => 0.089520220114
  | 7 => 0.090448914044
  | 8 => 0.091382378429
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12917 12917 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12917 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12917

/-! Actual upper energy certificates on all 43 source endpoints at 12917. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12917)
open BstLean.Part268 (cell12917)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12917 (gMinus 12917) (1 - (cell12917 i).lower) ≤ 1 ∧
    energyUpper 12917 (gMinus 12917) (BstLean.Part211.gPlus 12917)
      (finiteEnergy 12917 12917 0.011) (1 - (cell12917 i).lower) ≤
      (cell12917 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨10,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨11,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨12,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨13,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨14,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨15,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨16,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨17,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨18,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨19,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨20,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨21,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨22,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨23,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨24,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨25,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨26,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨27,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨28,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨29,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨30,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨31,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨32,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨33,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨34,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨35,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨36,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨37,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨38,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨39,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨40,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨41,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨42,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨43,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨44,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨45,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨46,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨47,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨48,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨49,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨50,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨51,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12917) (by norm_num)
        (q := 1 - (cell12917 ⟨52,by decide⟩).lower)
        (by norm_num [cell12917]) (by norm_num [cell12917])
      exact ⟨E.1,E.2.trans (by norm_num [cell12917])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12917

/-! Source-cell containment and simple scalar guards at 12917. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12917)
open BstLean.Part268 (cell12917)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12917 ⟨10,by decide⟩).lower ∧ (cell12917 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12917 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12917 ⟨11,by decide⟩).lower ∧ (cell12917 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12917 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12917 ⟨12,by decide⟩).lower ∧ (cell12917 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12917 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12917 ⟨13,by decide⟩).lower ∧ (cell12917 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12917 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12917 ⟨14,by decide⟩).lower ∧ (cell12917 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12917 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12917 ⟨15,by decide⟩).lower ∧ (cell12917 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12917 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12917 ⟨16,by decide⟩).lower ∧ (cell12917 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12917 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12917 ⟨17,by decide⟩).lower ∧ (cell12917 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12917 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12917 ⟨18,by decide⟩).lower ∧ (cell12917 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12917 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12917 ⟨19,by decide⟩).lower ∧ (cell12917 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12917 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12917 ⟨20,by decide⟩).lower ∧ (cell12917 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12917 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12917 ⟨21,by decide⟩).lower ∧ (cell12917 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12917 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12917 ⟨22,by decide⟩).lower ∧ (cell12917 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12917 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12917 ⟨23,by decide⟩).lower ∧ (cell12917 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12917 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12917 ⟨24,by decide⟩).lower ∧ (cell12917 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12917 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12917 ⟨25,by decide⟩).lower ∧ (cell12917 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12917 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12917 ⟨26,by decide⟩).lower ∧ (cell12917 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12917 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12917 ⟨27,by decide⟩).lower ∧ (cell12917 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12917 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12917 ⟨28,by decide⟩).lower ∧ (cell12917 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12917 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12917 ⟨29,by decide⟩).lower ∧ (cell12917 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12917 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12917 ⟨30,by decide⟩).lower ∧ (cell12917 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12917 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12917 ⟨31,by decide⟩).lower ∧ (cell12917 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12917 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12917 ⟨32,by decide⟩).lower ∧ (cell12917 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12917 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12917 ⟨33,by decide⟩).lower ∧ (cell12917 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12917 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12917 ⟨34,by decide⟩).lower ∧ (cell12917 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12917 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12917 ⟨35,by decide⟩).lower ∧ (cell12917 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12917 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12917 ⟨36,by decide⟩).lower ∧ (cell12917 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12917 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12917 ⟨37,by decide⟩).lower ∧ (cell12917 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12917 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12917 ⟨38,by decide⟩).lower ∧ (cell12917 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12917 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12917 ⟨39,by decide⟩).lower ∧ (cell12917 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12917 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12917 ⟨40,by decide⟩).lower ∧ (cell12917 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12917 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12917 ⟨41,by decide⟩).lower ∧ (cell12917 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12917 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12917 ⟨42,by decide⟩).lower ∧ (cell12917 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12917 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12917 ⟨43,by decide⟩).lower ∧ (cell12917 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12917 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12917 ⟨44,by decide⟩).lower ∧ (cell12917 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12917 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12917 ⟨45,by decide⟩).lower ∧ (cell12917 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12917 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12917 ⟨46,by decide⟩).lower ∧ (cell12917 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12917 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12917 ⟨47,by decide⟩).lower ∧ (cell12917 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12917 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12917 ⟨48,by decide⟩).lower ∧ (cell12917 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12917 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12917 ⟨49,by decide⟩).lower ∧ (cell12917 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12917 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12917 ⟨50,by decide⟩).lower ∧ (cell12917 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12917 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12917 ⟨51,by decide⟩).lower ∧ (cell12917 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12917 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12917 ⟨52,by decide⟩).lower ∧ (cell12917 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12917 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12917 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12917 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12917,cell12917,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12917 i).lower ∧
    (cell12917 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12917 i).upper ≤ (0.532 : ℝ) ∧
    (cell12917 i).centre ≤ (0.1 : ℝ) ∧ (cell12917 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12917 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12917 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12917

/-! The local source numeric instances at 12917 have no network premises. -/
namespace BstLean.Part269.N12917
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12917)
open BstLean.Part268 (cell12917)

noncomputable def sourceNumerics12917 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12917 (cell12917 i)
      scalarRow12917.M scalarRow12917.H scalarRow12917.xi := by
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
    energy_allowance := scalarRow12917.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12917]
    centre_nonneg := (scalarRow12917.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12917])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12917
/-! Actual 12918 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12918 ≤ (1.035503136670 : ℝ) := by
  have hr : (113.657379874779 : ℝ) ≤ √(12918 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.657379874779 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12918 12918 (11 / 1000) ≤
    (0.008410249895 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12918) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.657379874779 : ℝ) ≤ √(12918 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12918)
  have hdiv : K / √(12918 : ℝ) ≤ K / 113.657379874779 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.657379874779 ≤ (0.008410249895 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12918.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12918 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12918 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12918 := gPlus_lower 12918
end BstLean.Part269.N12918

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12918
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035503136669 : ℝ) ≤ wn 12918 := by
  have hn : √(12918 : ℝ) ≤ 113.657379874780 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12918 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.657379874780 ≤ 2 / √(12918 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247557033 : ℝ) ≤ rhoBar 12918 BstLean.Part154.csC ∧
    rhoBar 12918 BstLean.Part154.csC ≤ 0.000247557417 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035503136669 : ℝ) / (1.295212 * 12918) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035503136670 : ℝ) / (1.29521 * 12918) := by gcongr
      _ ≤ (0.000247557417 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12918 BstLean.Part154.csC) ≤ 0.000990290953 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12918 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) ≤ 0.000189085874 ∧
    cc1 (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) ≤ 0.000120316628 ∧
    cc2 (rhoBar 12918 BstLean.Part154.csC) ≤ 0.000069844762 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12918 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12918 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12918 BstLean.Part154.csC * nuR (rhoBar 12918 BstLean.Part154.csC)) ≤ 0.000495130156 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247557417 : ℝ) * 0.000990290953 := by gcongr
      _ ≤ (0.000495130156 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12918 BstLean.Part154.csC) * nuR (rhoBar 12918 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990290953 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12918 BstLean.Part154.csC) * rhoBar 12918 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247557417 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247557417 / 2 + 0.399 * 0.000990290953 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189085874 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495130156 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120316628 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247557417 / 1.414213562 := by gcongr
      _ ≤ (0.000069844762 : ℝ) := by norm_num

end BstLean.Part269.N12918

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12918
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) ≤ 1.54402E-7 := by
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12918 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12918 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12918 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189085874 : ℝ) ^ 2 + 0.000120316628 ^ 2 + 3 * 0.000069844762 ^ 2 +
        2 * 0.797885 * 0.000189085874 * 0.000120316628 + 2 * 0.000189085874 * 0.000069844762 +
        4 * 0.797885 * 0.000120316628 * 0.000069844762 := by gcongr
    _ ≤ (1.54402E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12918 BstLean.Part154.csC Θ ≤ 0.002583384579 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12918 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12918 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12918 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035503136670 * 1.54402E-7 / (0.000247557033 : ℝ) := by gcongr
    _ ≤ 0.002583384579 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12918 BstLean.Part154.csC Θ ≤ 0.002865561021 + 0.000652781092 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12918 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12918 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035503136670 : ℝ) * ((2 * Θ * 0.000247557417 +
        (6863 / 10000) * 0.000247557417 * 12918 * 0.000990290953) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002865561021 + 0.000652781092 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12918 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12918 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12918 0.011 Θ ∧ gammaRatio 12918 0.011 Θ ≤ 0.000085103838 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12918 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035503136670 : ℝ) * 0.525 / ((1 - 0.011) * 12918) := by gcongr
      _ ≤ (0.000085103838 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12918 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12918 0.011 Θ) :=
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
    badAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12918 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12918 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12918 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12918 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12918 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12918 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12918 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12918 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12918 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12918 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035503136670 : ℝ) * 12918 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003329232038 + 0.003236165671 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12918

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12918
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12918 BstLean.Part154.csC) (piBar (rhoBar 12918 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12918 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12918 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12918 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12918 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12918 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12918 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12918 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12918 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12918 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12918 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052034792690 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12918) ≤ 0.010507347454 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12918 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035503136670)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010507347454 + 2 * 0.737676 / 12918) := by gcongr
    _ ≤ (0.052034792690 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12918 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12918

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12918
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513260527 : ℝ) ≤ plow 12918 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12918) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534819016)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356276904) : eMP 12918 0.011 xi bn ≤ 0.001167921949 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12918 : ℝ) * (1 - 0.011))) ≤ 0.000577501821 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356276904 / (12918 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577501821 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577501821 : ℝ) + 3.141593 * 0.052534819016 / (12918 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167921949 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534819016)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356276904) : PiBarMP 12918 12 0.011 xi bn ≤ 0.159871032938 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12918 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036827664928 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.030535697217 : ℝ) ≤ √((12918 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.657379874779 : ℝ) ≤ √(12918 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12918) ≤ 0.122582521946 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036827664928 + 0.052534819016 * 1.772454 / (2 * (113.030535697217 : ℝ))) * (1 + 0.001167921949) +
        8 / (12918 * 113.657379874779) + 0.122582521946 := by gcongr
    _ ≤ (0.159871032938 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534819016)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356276904) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281239546167) :
    parallelOracle 12918 0.011 xi bn cd ≤ 0.160844699678 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12918 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12918 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513260527 : ℝ) ≤ plow 12918 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.657379874779 : ℝ) ≤ √(12918 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281239546167 : ℝ) / (2 * 0.560513260527 * 113.657379874779)) * 0.159871032938 +
        0.281239546167 ^ 2 / (2 * 0.560513260527 * 113.657379874779) := by gcongr
    _ ≤ (0.160844699678 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534819016) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356276904)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281239546167) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12918 12918 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513260527 : ℝ) ≤ plow 12918 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.657379874779 : ℝ) ≤ √(12918 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12918 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12918 Θ 1.22 ≤ 0.011667526574 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.657379874779 := by gcongr <;> linarith
      _ ≤ (0.011667526574 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12918 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12918 12918 0.011 ≤ 0.008410249895 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12918 12918 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12918 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12918 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12918 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12918 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160844699678 + 0.011667526574 + (0.008410249895 : ℝ) *
        (1 + 2 * (0.281239546167 + 0.011667526574) / (0.560513260527 * 113.657379874779))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12918]

end BstLean.Part269.N12918

/-! The original eight local profiles supply actual 12918 moment certificates. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12918 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052534819016 ∧
    0 ≤ bN 12918 BstLean.Part154.csC (groupTheta g) ∧ bN 12918 BstLean.Part154.csC (groupTheta g) ≤ 0.001356276904 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12918 12918 0.011
      (momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12918 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12918 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12918 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229204753477 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12918 0.011
      (momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12918 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12918
/-! The actual computed-centre upper energy formula at 12918. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12918

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12918)
open BstLean.Part268 (cell12918)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084878490752
  | 2 => 0.085810524354
  | 3 => 0.086739220478
  | 4 => 0.087665651210
  | 5 => 0.088591123744
  | 6 => 0.089517216623
  | 7 => 0.090445819630
  | 8 => 0.091379177423
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12918 12918 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12918 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12918

/-! Actual upper energy certificates on all 43 source endpoints at 12918. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12918)
open BstLean.Part268 (cell12918)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12918 (gMinus 12918) (1 - (cell12918 i).lower) ≤ 1 ∧
    energyUpper 12918 (gMinus 12918) (BstLean.Part211.gPlus 12918)
      (finiteEnergy 12918 12918 0.011) (1 - (cell12918 i).lower) ≤
      (cell12918 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨10,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨11,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨12,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨13,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨14,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨15,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨16,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨17,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨18,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨19,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨20,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨21,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨22,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨23,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨24,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨25,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨26,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨27,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨28,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨29,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨30,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨31,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨32,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨33,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨34,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨35,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨36,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨37,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨38,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨39,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨40,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨41,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨42,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨43,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨44,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨45,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨46,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨47,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨48,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨49,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨50,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨51,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12918) (by norm_num)
        (q := 1 - (cell12918 ⟨52,by decide⟩).lower)
        (by norm_num [cell12918]) (by norm_num [cell12918])
      exact ⟨E.1,E.2.trans (by norm_num [cell12918])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12918

/-! Source-cell containment and simple scalar guards at 12918. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12918)
open BstLean.Part268 (cell12918)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12918 ⟨10,by decide⟩).lower ∧ (cell12918 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12918 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12918 ⟨11,by decide⟩).lower ∧ (cell12918 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12918 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12918 ⟨12,by decide⟩).lower ∧ (cell12918 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12918 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12918 ⟨13,by decide⟩).lower ∧ (cell12918 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12918 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12918 ⟨14,by decide⟩).lower ∧ (cell12918 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12918 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12918 ⟨15,by decide⟩).lower ∧ (cell12918 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12918 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12918 ⟨16,by decide⟩).lower ∧ (cell12918 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12918 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12918 ⟨17,by decide⟩).lower ∧ (cell12918 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12918 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12918 ⟨18,by decide⟩).lower ∧ (cell12918 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12918 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12918 ⟨19,by decide⟩).lower ∧ (cell12918 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12918 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12918 ⟨20,by decide⟩).lower ∧ (cell12918 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12918 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12918 ⟨21,by decide⟩).lower ∧ (cell12918 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12918 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12918 ⟨22,by decide⟩).lower ∧ (cell12918 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12918 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12918 ⟨23,by decide⟩).lower ∧ (cell12918 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12918 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12918 ⟨24,by decide⟩).lower ∧ (cell12918 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12918 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12918 ⟨25,by decide⟩).lower ∧ (cell12918 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12918 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12918 ⟨26,by decide⟩).lower ∧ (cell12918 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12918 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12918 ⟨27,by decide⟩).lower ∧ (cell12918 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12918 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12918 ⟨28,by decide⟩).lower ∧ (cell12918 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12918 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12918 ⟨29,by decide⟩).lower ∧ (cell12918 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12918 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12918 ⟨30,by decide⟩).lower ∧ (cell12918 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12918 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12918 ⟨31,by decide⟩).lower ∧ (cell12918 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12918 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12918 ⟨32,by decide⟩).lower ∧ (cell12918 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12918 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12918 ⟨33,by decide⟩).lower ∧ (cell12918 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12918 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12918 ⟨34,by decide⟩).lower ∧ (cell12918 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12918 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12918 ⟨35,by decide⟩).lower ∧ (cell12918 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12918 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12918 ⟨36,by decide⟩).lower ∧ (cell12918 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12918 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12918 ⟨37,by decide⟩).lower ∧ (cell12918 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12918 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12918 ⟨38,by decide⟩).lower ∧ (cell12918 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12918 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12918 ⟨39,by decide⟩).lower ∧ (cell12918 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12918 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12918 ⟨40,by decide⟩).lower ∧ (cell12918 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12918 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12918 ⟨41,by decide⟩).lower ∧ (cell12918 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12918 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12918 ⟨42,by decide⟩).lower ∧ (cell12918 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12918 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12918 ⟨43,by decide⟩).lower ∧ (cell12918 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12918 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12918 ⟨44,by decide⟩).lower ∧ (cell12918 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12918 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12918 ⟨45,by decide⟩).lower ∧ (cell12918 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12918 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12918 ⟨46,by decide⟩).lower ∧ (cell12918 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12918 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12918 ⟨47,by decide⟩).lower ∧ (cell12918 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12918 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12918 ⟨48,by decide⟩).lower ∧ (cell12918 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12918 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12918 ⟨49,by decide⟩).lower ∧ (cell12918 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12918 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12918 ⟨50,by decide⟩).lower ∧ (cell12918 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12918 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12918 ⟨51,by decide⟩).lower ∧ (cell12918 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12918 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12918 ⟨52,by decide⟩).lower ∧ (cell12918 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12918 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12918 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12918 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12918,cell12918,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12918 i).lower ∧
    (cell12918 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12918 i).upper ≤ (0.532 : ℝ) ∧
    (cell12918 i).centre ≤ (0.1 : ℝ) ∧ (cell12918 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12918 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12918 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12918

/-! The local source numeric instances at 12918 have no network premises. -/
namespace BstLean.Part269.N12918
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12918)
open BstLean.Part268 (cell12918)

noncomputable def sourceNumerics12918 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12918 (cell12918 i)
      scalarRow12918.M scalarRow12918.H scalarRow12918.xi := by
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
    energy_allowance := scalarRow12918.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12918]
    centre_nonneg := (scalarRow12918.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12918])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12918
/-! Actual 12919 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12919 ≤ (1.035501750593 : ℝ) := by
  have hr : (113.661778976048 : ℝ) ≤ √(12919 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.661778976048 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12919 12919 (11 / 1000) ≤
    (0.008409924387 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12919) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.661778976048 : ℝ) ≤ √(12919 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12919)
  have hdiv : K / √(12919 : ℝ) ≤ K / 113.661778976048 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.661778976048 ≤ (0.008409924387 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12919.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12919 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12919 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12919 := gPlus_lower 12919
end BstLean.Part269.N12919

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12919
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035501750592 : ℝ) ≤ wn 12919 := by
  have hn : √(12919 : ℝ) ≤ 113.661778976049 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12919 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.661778976049 ≤ 2 / √(12919 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247537540 : ℝ) ≤ rhoBar 12919 BstLean.Part154.csC ∧
    rhoBar 12919 BstLean.Part154.csC ≤ 0.000247537923 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035501750592 : ℝ) / (1.295212 * 12919) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035501750593 : ℝ) / (1.29521 * 12919) := by gcongr
      _ ≤ (0.000247537923 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12919 BstLean.Part154.csC) ≤ 0.000990212968 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12919 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) ≤ 0.000189070984 ∧
    cc1 (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) ≤ 0.000120307154 ∧
    cc2 (rhoBar 12919 BstLean.Part154.csC) ≤ 0.000069839262 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12919 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12919 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12919 BstLean.Part154.csC * nuR (rhoBar 12919 BstLean.Part154.csC)) ≤ 0.000495091165 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247537923 : ℝ) * 0.000990212968 := by gcongr
      _ ≤ (0.000495091165 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12919 BstLean.Part154.csC) * nuR (rhoBar 12919 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990212968 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12919 BstLean.Part154.csC) * rhoBar 12919 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247537923 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247537923 / 2 + 0.399 * 0.000990212968 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189070984 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495091165 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120307154 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247537923 / 1.414213562 := by gcongr
      _ ≤ (0.000069839262 : ℝ) := by norm_num

end BstLean.Part269.N12919

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12919
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) ≤ 1.54378E-7 := by
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12919 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12919 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12919 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189070984 : ℝ) ^ 2 + 0.000120307154 ^ 2 + 3 * 0.000069839262 ^ 2 +
        2 * 0.797885 * 0.000189070984 * 0.000120307154 + 2 * 0.000189070984 * 0.000069839262 +
        4 * 0.797885 * 0.000120307154 * 0.000069839262 := by gcongr
    _ ≤ (1.54378E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12919 BstLean.Part154.csC Θ ≤ 0.002583182967 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12919 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12919 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12919 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035501750593 * 1.54378E-7 / (0.000247537540 : ℝ) := by gcongr
    _ ≤ 0.002583182967 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12919 BstLean.Part154.csC Θ ≤ 0.002865327684 + 0.000652728815 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12919 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12919 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035501750593 : ℝ) * ((2 * Θ * 0.000247537923 +
        (6863 / 10000) * 0.000247537923 * 12919 * 0.000990212968) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002865327684 + 0.000652728815 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12919 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12919 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12919 0.011 Θ ∧ gammaRatio 12919 0.011 Θ ≤ 0.000085097137 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12919 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035501750593 : ℝ) * 0.525 / ((1 - 0.011) * 12919) := by gcongr
      _ ≤ (0.000085097137 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12919 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12919 0.011 Θ) :=
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
    badAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12919 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12919 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12919 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12919 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12919 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12919 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12919 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12919 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12919 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12919 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035501750593 : ℝ) * 12919 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003328998701 + 0.003235911782 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12919

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12919
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12919 BstLean.Part154.csC) (piBar (rhoBar 12919 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12919 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12919 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12919 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12919 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12919 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12919 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12919 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12919 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12919 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12919 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052032757113 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12919) ≤ 0.010506940784 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12919 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035501750593)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010506940784 + 2 * 0.737676 / 12919) := by gcongr
    _ ≤ (0.052032757113 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12919 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12919

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12919
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513304234 : ℝ) ≤ plow 12919 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12919) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534452387)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356171058) : eMP 12919 0.011 xi bn ≤ 0.001167831087 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12919 : ℝ) * (1 - 0.011))) ≤ 0.000577456935 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356171058 / (12919 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577456935 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577456935 : ℝ) + 3.141593 * 0.052534452387 / (12919 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167831087 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534452387)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356171058) : PiBarMP 12919 12 0.011 xi bn ≤ 0.159864826967 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12919 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036826227855 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.034910536524 : ℝ) ≤ √((12919 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.661778976048 : ℝ) ≤ √(12919 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12919) ≤ 0.122577777581 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036826227855 + 0.052534452387 * 1.772454 / (2 * (113.034910536524 : ℝ))) * (1 + 0.001167831087) +
        8 / (12919 * 113.661778976048) + 0.122577777581 := by gcongr
    _ ≤ (0.159864826967 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534452387)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356171058) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281236710803) :
    parallelOracle 12919 0.011 xi bn cd ≤ 0.160838426175 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12919 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12919 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513304234 : ℝ) ≤ plow 12919 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.661778976048 : ℝ) ≤ √(12919 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281236710803 : ℝ) / (2 * 0.560513304234 * 113.661778976048)) * 0.159864826967 +
        0.281236710803 ^ 2 / (2 * 0.560513304234 * 113.661778976048) := by gcongr
    _ ≤ (0.160838426175 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534452387) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356171058)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281236710803) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12919 12919 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513304234 : ℝ) ≤ plow 12919 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.661778976048 : ℝ) ≤ √(12919 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12919 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12919 Θ 1.22 ≤ 0.011667075001 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.661778976048 := by gcongr <;> linarith
      _ ≤ (0.011667075001 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12919 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12919 12919 0.011 ≤ 0.008409924387 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12919 12919 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12919 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12919 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12919 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12919 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160838426175 + 0.011667075001 + (0.008409924387 : ℝ) *
        (1 + 2 * (0.281236710803 + 0.011667075001) / (0.560513304234 * 113.661778976048))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12919]

end BstLean.Part269.N12919

/-! The original eight local profiles supply actual 12919 moment certificates. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12919 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052534452387 ∧
    0 ≤ bN 12919 BstLean.Part154.csC (groupTheta g) ∧ bN 12919 BstLean.Part154.csC (groupTheta g) ≤ 0.001356171058 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12919 12919 0.011
      (momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12919 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12919 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12919 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229203953690 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12919 0.011
      (momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12919 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12919
/-! The actual computed-centre upper energy formula at 12919. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12919

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12919)
open BstLean.Part268 (cell12919)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084875787383
  | 2 => 0.085807775876
  | 3 => 0.086736421068
  | 4 => 0.087662793653
  | 5 => 0.088588199183
  | 6 => 0.089514214272
  | 7 => 0.090442726448
  | 8 => 0.091375977760
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12919 12919 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12919 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12919

/-! Actual upper energy certificates on all 43 source endpoints at 12919. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12919)
open BstLean.Part268 (cell12919)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12919 (gMinus 12919) (1 - (cell12919 i).lower) ≤ 1 ∧
    energyUpper 12919 (gMinus 12919) (BstLean.Part211.gPlus 12919)
      (finiteEnergy 12919 12919 0.011) (1 - (cell12919 i).lower) ≤
      (cell12919 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨10,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨11,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨12,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨13,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨14,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨15,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨16,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨17,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨18,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨19,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨20,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨21,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨22,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨23,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨24,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨25,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨26,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨27,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨28,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨29,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨30,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨31,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨32,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨33,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨34,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨35,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨36,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨37,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨38,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨39,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨40,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨41,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨42,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨43,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨44,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨45,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨46,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨47,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨48,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨49,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨50,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨51,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12919) (by norm_num)
        (q := 1 - (cell12919 ⟨52,by decide⟩).lower)
        (by norm_num [cell12919]) (by norm_num [cell12919])
      exact ⟨E.1,E.2.trans (by norm_num [cell12919])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12919

/-! Source-cell containment and simple scalar guards at 12919. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12919)
open BstLean.Part268 (cell12919)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12919 ⟨10,by decide⟩).lower ∧ (cell12919 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12919 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12919 ⟨11,by decide⟩).lower ∧ (cell12919 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12919 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12919 ⟨12,by decide⟩).lower ∧ (cell12919 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12919 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12919 ⟨13,by decide⟩).lower ∧ (cell12919 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12919 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12919 ⟨14,by decide⟩).lower ∧ (cell12919 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12919 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12919 ⟨15,by decide⟩).lower ∧ (cell12919 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12919 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12919 ⟨16,by decide⟩).lower ∧ (cell12919 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12919 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12919 ⟨17,by decide⟩).lower ∧ (cell12919 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12919 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12919 ⟨18,by decide⟩).lower ∧ (cell12919 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12919 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12919 ⟨19,by decide⟩).lower ∧ (cell12919 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12919 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12919 ⟨20,by decide⟩).lower ∧ (cell12919 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12919 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12919 ⟨21,by decide⟩).lower ∧ (cell12919 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12919 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12919 ⟨22,by decide⟩).lower ∧ (cell12919 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12919 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12919 ⟨23,by decide⟩).lower ∧ (cell12919 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12919 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12919 ⟨24,by decide⟩).lower ∧ (cell12919 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12919 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12919 ⟨25,by decide⟩).lower ∧ (cell12919 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12919 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12919 ⟨26,by decide⟩).lower ∧ (cell12919 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12919 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12919 ⟨27,by decide⟩).lower ∧ (cell12919 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12919 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12919 ⟨28,by decide⟩).lower ∧ (cell12919 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12919 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12919 ⟨29,by decide⟩).lower ∧ (cell12919 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12919 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12919 ⟨30,by decide⟩).lower ∧ (cell12919 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12919 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12919 ⟨31,by decide⟩).lower ∧ (cell12919 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12919 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12919 ⟨32,by decide⟩).lower ∧ (cell12919 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12919 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12919 ⟨33,by decide⟩).lower ∧ (cell12919 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12919 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12919 ⟨34,by decide⟩).lower ∧ (cell12919 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12919 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12919 ⟨35,by decide⟩).lower ∧ (cell12919 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12919 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12919 ⟨36,by decide⟩).lower ∧ (cell12919 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12919 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12919 ⟨37,by decide⟩).lower ∧ (cell12919 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12919 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12919 ⟨38,by decide⟩).lower ∧ (cell12919 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12919 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12919 ⟨39,by decide⟩).lower ∧ (cell12919 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12919 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12919 ⟨40,by decide⟩).lower ∧ (cell12919 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12919 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12919 ⟨41,by decide⟩).lower ∧ (cell12919 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12919 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12919 ⟨42,by decide⟩).lower ∧ (cell12919 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12919 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12919 ⟨43,by decide⟩).lower ∧ (cell12919 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12919 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12919 ⟨44,by decide⟩).lower ∧ (cell12919 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12919 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12919 ⟨45,by decide⟩).lower ∧ (cell12919 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12919 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12919 ⟨46,by decide⟩).lower ∧ (cell12919 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12919 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12919 ⟨47,by decide⟩).lower ∧ (cell12919 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12919 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12919 ⟨48,by decide⟩).lower ∧ (cell12919 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12919 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12919 ⟨49,by decide⟩).lower ∧ (cell12919 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12919 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12919 ⟨50,by decide⟩).lower ∧ (cell12919 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12919 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12919 ⟨51,by decide⟩).lower ∧ (cell12919 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12919 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12919 ⟨52,by decide⟩).lower ∧ (cell12919 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12919 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12919 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12919 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12919,cell12919,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12919 i).lower ∧
    (cell12919 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12919 i).upper ≤ (0.532 : ℝ) ∧
    (cell12919 i).centre ≤ (0.1 : ℝ) ∧ (cell12919 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12919 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12919 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12919

/-! The local source numeric instances at 12919 have no network premises. -/
namespace BstLean.Part269.N12919
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12919)
open BstLean.Part268 (cell12919)

noncomputable def sourceNumerics12919 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12919 (cell12919 i)
      scalarRow12919.M scalarRow12919.H scalarRow12919.xi := by
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
    energy_allowance := scalarRow12919.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12919]
    centre_nonneg := (scalarRow12919.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12919])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12919
/-! Actual 12920 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12920 ≤ (1.035500364678 : ℝ) := by
  have hr : (113.666177907062 : ℝ) ≤ √(12920 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.666177907062 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12920 12920 (11 / 1000) ≤
    (0.008409598916 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12920) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.666177907062 : ℝ) ≤ √(12920 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12920)
  have hdiv : K / √(12920 : ℝ) ≤ K / 113.666177907062 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.666177907062 ≤ (0.008409598916 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12920.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12920 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12920 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12920 := gPlus_lower 12920
end BstLean.Part269.N12920

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12920
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035500364677 : ℝ) ≤ wn 12920 := by
  have hn : √(12920 : ℝ) ≤ 113.666177907063 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12920 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.666177907063 ≤ 2 / √(12920 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247518049 : ℝ) ≤ rhoBar 12920 BstLean.Part154.csC ∧
    rhoBar 12920 BstLean.Part154.csC ≤ 0.000247518432 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035500364677 : ℝ) / (1.295212 * 12920) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035500364678 : ℝ) / (1.29521 * 12920) := by gcongr
      _ ≤ (0.000247518432 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12920 BstLean.Part154.csC) ≤ 0.000990134994 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12920 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) ≤ 0.000189056096 ∧
    cc1 (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) ≤ 0.000120297680 ∧
    cc2 (rhoBar 12920 BstLean.Part154.csC) ≤ 0.000069833763 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12920 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12920 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12920 BstLean.Part154.csC * nuR (rhoBar 12920 BstLean.Part154.csC)) ≤ 0.000495052181 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247518432 : ℝ) * 0.000990134994 := by gcongr
      _ ≤ (0.000495052181 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12920 BstLean.Part154.csC) * nuR (rhoBar 12920 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990134994 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12920 BstLean.Part154.csC) * rhoBar 12920 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247518432 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247518432 / 2 + 0.399 * 0.000990134994 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189056096 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495052181 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120297680 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247518432 / 1.414213562 := by gcongr
      _ ≤ (0.000069833763 : ℝ) := by norm_num

end BstLean.Part269.N12920

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12920
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) ≤ 1.54354E-7 := by
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12920 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12920 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12920 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189056096 : ℝ) ^ 2 + 0.000120297680 ^ 2 + 3 * 0.000069833763 ^ 2 +
        2 * 0.797885 * 0.000189056096 * 0.000120297680 + 2 * 0.000189056096 * 0.000069833763 +
        4 * 0.797885 * 0.000120297680 * 0.000069833763 := by gcongr
    _ ≤ (1.54354E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12920 BstLean.Part154.csC Θ ≤ 0.002582981305 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12920 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12920 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12920 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035500364678 * 1.54354E-7 / (0.000247518049 : ℝ) := by gcongr
    _ ≤ 0.002582981305 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12920 BstLean.Part154.csC Θ ≤ 0.002865094381 + 0.000652676546 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12920 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12920 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035500364678 : ℝ) * ((2 * Θ * 0.000247518432 +
        (6863 / 10000) * 0.000247518432 * 12920 * 0.000990134994) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002865094381 + 0.000652676546 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12920 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12920 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12920 0.011 Θ ∧ gammaRatio 12920 0.011 Θ ≤ 0.000085090437 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12920 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035500364678 : ℝ) * 0.525 / ((1 - 0.011) * 12920) := by gcongr
      _ ≤ (0.000085090437 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12920 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12920 0.011 Θ) :=
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
    badAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12920 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12920 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12920 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12920 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12920 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12920 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12920 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12920 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12920 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12920 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035500364678 : ℝ) * 12920 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003328765398 + 0.003235657851 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12920

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12920
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12920 BstLean.Part154.csC) (piBar (rhoBar 12920 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12920 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12920 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12920 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12920 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12920 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12920 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12920 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12920 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12920 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12920 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052030721773 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12920) ≤ 0.010506534161 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12920 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035500364678)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010506534161 + 2 * 0.737676 / 12920) := by gcongr
    _ ≤ (0.052030721773 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12920 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12920

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12920
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513347933 : ℝ) ≤ plow 12920 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12920) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534085770)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356065186) : eMP 12920 0.011 xi bn ≤ 0.001167740223 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12920 : ℝ) * (1 - 0.011))) ≤ 0.000577412048 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356065186 / (12920 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577412048 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577412048 : ℝ) + 3.141593 * 0.052534085770 / (12920 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167740223 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534085770)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356065186) : PiBarMP 12920 12 0.011 xi bn ≤ 0.159858621140 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12920 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036824790373 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.039285206515 : ℝ) ≤ √((12920 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.666177907062 : ℝ) ≤ √(12920 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12920) ≤ 0.122573033767 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036824790373 + 0.052534085770 * 1.772454 / (2 * (113.039285206515 : ℝ))) * (1 + 0.001167740223) +
        8 / (12920 * 113.666177907062) + 0.122573033767 := by gcongr
    _ ≤ (0.159858621140 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534085770)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356065186) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281233875700) :
    parallelOracle 12920 0.011 xi bn cd ≤ 0.160832152825 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12920 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12920 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513347933 : ℝ) ≤ plow 12920 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.666177907062 : ℝ) ≤ √(12920 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281233875700 : ℝ) / (2 * 0.560513347933 * 113.666177907062)) * 0.159858621140 +
        0.281233875700 ^ 2 / (2 * 0.560513347933 * 113.666177907062) := by gcongr
    _ ≤ (0.160832152825 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052534085770) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356065186)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281233875700) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12920 12920 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513347933 : ℝ) ≤ plow 12920 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.666177907062 : ℝ) ≤ √(12920 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12920 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12920 Θ 1.22 ≤ 0.011666623480 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.666177907062 := by gcongr <;> linarith
      _ ≤ (0.011666623480 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12920 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12920 12920 0.011 ≤ 0.008409598916 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12920 12920 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12920 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12920 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12920 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12920 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160832152825 + 0.011666623480 + (0.008409598916 : ℝ) *
        (1 + 2 * (0.281233875700 + 0.011666623480) / (0.560513347933 * 113.666177907062))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12920]

end BstLean.Part269.N12920

/-! The original eight local profiles supply actual 12920 moment certificates. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12920 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052534085770 ∧
    0 ≤ bN 12920 BstLean.Part154.csC (groupTheta g) ∧ bN 12920 BstLean.Part154.csC (groupTheta g) ≤ 0.001356065186 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12920 12920 0.011
      (momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12920 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12920 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12920 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229203153927 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12920 0.011
      (momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12920 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12920
/-! The actual computed-centre upper energy formula at 12920. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12920

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12920)
open BstLean.Part268 (cell12920)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084873084888
  | 2 => 0.085805028307
  | 3 => 0.086733622607
  | 4 => 0.087659937097
  | 5 => 0.088585275686
  | 6 => 0.089511213059
  | 7 => 0.090439634498
  | 8 => 0.091372779441
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12920 12920 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12920 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12920

/-! Actual upper energy certificates on all 43 source endpoints at 12920. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12920)
open BstLean.Part268 (cell12920)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12920 (gMinus 12920) (1 - (cell12920 i).lower) ≤ 1 ∧
    energyUpper 12920 (gMinus 12920) (BstLean.Part211.gPlus 12920)
      (finiteEnergy 12920 12920 0.011) (1 - (cell12920 i).lower) ≤
      (cell12920 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨10,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨11,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨12,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨13,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨14,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨15,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨16,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨17,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨18,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨19,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨20,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨21,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨22,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨23,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨24,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨25,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨26,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨27,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨28,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨29,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨30,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨31,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨32,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨33,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨34,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨35,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨36,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨37,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨38,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨39,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨40,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨41,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨42,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨43,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨44,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨45,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨46,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨47,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨48,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨49,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨50,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨51,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12920) (by norm_num)
        (q := 1 - (cell12920 ⟨52,by decide⟩).lower)
        (by norm_num [cell12920]) (by norm_num [cell12920])
      exact ⟨E.1,E.2.trans (by norm_num [cell12920])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12920

/-! Source-cell containment and simple scalar guards at 12920. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12920)
open BstLean.Part268 (cell12920)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12920 ⟨10,by decide⟩).lower ∧ (cell12920 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12920 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12920 ⟨11,by decide⟩).lower ∧ (cell12920 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12920 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12920 ⟨12,by decide⟩).lower ∧ (cell12920 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12920 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12920 ⟨13,by decide⟩).lower ∧ (cell12920 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12920 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12920 ⟨14,by decide⟩).lower ∧ (cell12920 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12920 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12920 ⟨15,by decide⟩).lower ∧ (cell12920 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12920 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12920 ⟨16,by decide⟩).lower ∧ (cell12920 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12920 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12920 ⟨17,by decide⟩).lower ∧ (cell12920 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12920 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12920 ⟨18,by decide⟩).lower ∧ (cell12920 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12920 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12920 ⟨19,by decide⟩).lower ∧ (cell12920 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12920 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12920 ⟨20,by decide⟩).lower ∧ (cell12920 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12920 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12920 ⟨21,by decide⟩).lower ∧ (cell12920 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12920 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12920 ⟨22,by decide⟩).lower ∧ (cell12920 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12920 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12920 ⟨23,by decide⟩).lower ∧ (cell12920 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12920 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12920 ⟨24,by decide⟩).lower ∧ (cell12920 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12920 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12920 ⟨25,by decide⟩).lower ∧ (cell12920 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12920 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12920 ⟨26,by decide⟩).lower ∧ (cell12920 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12920 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12920 ⟨27,by decide⟩).lower ∧ (cell12920 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12920 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12920 ⟨28,by decide⟩).lower ∧ (cell12920 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12920 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12920 ⟨29,by decide⟩).lower ∧ (cell12920 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12920 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12920 ⟨30,by decide⟩).lower ∧ (cell12920 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12920 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12920 ⟨31,by decide⟩).lower ∧ (cell12920 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12920 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12920 ⟨32,by decide⟩).lower ∧ (cell12920 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12920 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12920 ⟨33,by decide⟩).lower ∧ (cell12920 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12920 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12920 ⟨34,by decide⟩).lower ∧ (cell12920 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12920 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12920 ⟨35,by decide⟩).lower ∧ (cell12920 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12920 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12920 ⟨36,by decide⟩).lower ∧ (cell12920 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12920 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12920 ⟨37,by decide⟩).lower ∧ (cell12920 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12920 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12920 ⟨38,by decide⟩).lower ∧ (cell12920 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12920 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12920 ⟨39,by decide⟩).lower ∧ (cell12920 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12920 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12920 ⟨40,by decide⟩).lower ∧ (cell12920 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12920 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12920 ⟨41,by decide⟩).lower ∧ (cell12920 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12920 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12920 ⟨42,by decide⟩).lower ∧ (cell12920 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12920 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12920 ⟨43,by decide⟩).lower ∧ (cell12920 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12920 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12920 ⟨44,by decide⟩).lower ∧ (cell12920 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12920 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12920 ⟨45,by decide⟩).lower ∧ (cell12920 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12920 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12920 ⟨46,by decide⟩).lower ∧ (cell12920 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12920 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12920 ⟨47,by decide⟩).lower ∧ (cell12920 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12920 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12920 ⟨48,by decide⟩).lower ∧ (cell12920 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12920 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12920 ⟨49,by decide⟩).lower ∧ (cell12920 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12920 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12920 ⟨50,by decide⟩).lower ∧ (cell12920 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12920 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12920 ⟨51,by decide⟩).lower ∧ (cell12920 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12920 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12920 ⟨52,by decide⟩).lower ∧ (cell12920 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12920 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12920 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12920 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12920,cell12920,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12920 i).lower ∧
    (cell12920 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12920 i).upper ≤ (0.532 : ℝ) ∧
    (cell12920 i).centre ≤ (0.1 : ℝ) ∧ (cell12920 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12920 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12920 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12920

/-! The local source numeric instances at 12920 have no network premises. -/
namespace BstLean.Part269.N12920
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12920)
open BstLean.Part268 (cell12920)

noncomputable def sourceNumerics12920 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12920 (cell12920 i)
      scalarRow12920.M scalarRow12920.H scalarRow12920.xi := by
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
    energy_allowance := scalarRow12920.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12920]
    centre_nonneg := (scalarRow12920.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12920])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12920
/-! Actual 12921 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12921 ≤ (1.035498978924 : ℝ) := by
  have hr : (113.670576667843 : ℝ) ≤ √(12921 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.670576667843 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12921 12921 (11 / 1000) ≤
    (0.008409273484 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12921) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.670576667843 : ℝ) ≤ √(12921 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12921)
  have hdiv : K / √(12921 : ℝ) ≤ K / 113.670576667843 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.670576667843 ≤ (0.008409273484 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12921.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12921 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12921 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12921 := gPlus_lower 12921
end BstLean.Part269.N12921

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12921
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035498978923 : ℝ) ≤ wn 12921 := by
  have hn : √(12921 : ℝ) ≤ 113.670576667844 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12921 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.670576667844 ≤ 2 / √(12921 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247498562 : ℝ) ≤ rhoBar 12921 BstLean.Part154.csC ∧
    rhoBar 12921 BstLean.Part154.csC ≤ 0.000247498945 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035498978923 : ℝ) / (1.295212 * 12921) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035498978924 : ℝ) / (1.29521 * 12921) := by gcongr
      _ ≤ (0.000247498945 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12921 BstLean.Part154.csC) ≤ 0.000990057036 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12921 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) ≤ 0.000189041211 ∧
    cc1 (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) ≤ 0.000120288209 ∧
    cc2 (rhoBar 12921 BstLean.Part154.csC) ≤ 0.000069828265 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12921 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12921 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12921 BstLean.Part154.csC * nuR (rhoBar 12921 BstLean.Part154.csC)) ≤ 0.000495013204 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247498945 : ℝ) * 0.000990057036 := by gcongr
      _ ≤ (0.000495013204 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12921 BstLean.Part154.csC) * nuR (rhoBar 12921 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990057036 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12921 BstLean.Part154.csC) * rhoBar 12921 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247498945 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247498945 / 2 + 0.399 * 0.000990057036 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189041211 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495013204 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120288209 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247498945 / 1.414213562 := by gcongr
      _ ≤ (0.000069828265 : ℝ) := by norm_num

end BstLean.Part269.N12921

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12921
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) ≤ 1.54329E-7 := by
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12921 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12921 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12921 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189041211 : ℝ) ^ 2 + 0.000120288209 ^ 2 + 3 * 0.000069828265 ^ 2 +
        2 * 0.797885 * 0.000189041211 * 0.000120288209 + 2 * 0.000189041211 * 0.000069828265 +
        4 * 0.797885 * 0.000120288209 * 0.000069828265 := by gcongr
    _ ≤ (1.54329E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12921 BstLean.Part154.csC Θ ≤ 0.002582762836 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12921 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12921 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12921 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035498978924 * 1.54329E-7 / (0.000247498562 : ℝ) := by gcongr
    _ ≤ 0.002582762836 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12921 BstLean.Part154.csC Θ ≤ 0.002864861136 + 0.000652624287 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12921 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12921 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035498978924 : ℝ) * ((2 * Θ * 0.000247498945 +
        (6863 / 10000) * 0.000247498945 * 12921 * 0.000990057036) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002864861136 + 0.000652624287 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12921 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12921 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12921 0.011 Θ ∧ gammaRatio 12921 0.011 Θ ≤ 0.000085083737 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12921 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035498978924 : ℝ) * 0.525 / ((1 - 0.011) * 12921) := by gcongr
      _ ≤ (0.000085083737 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12921 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12921 0.011 Θ) :=
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
    badAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12921 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12921 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12921 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12921 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12921 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12921 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12921 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12921 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12921 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12921 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035498978924 : ℝ) * 12921 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003328532153 + 0.003235387123 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12921

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12921
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12921 BstLean.Part154.csC) (piBar (rhoBar 12921 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12921 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12921 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12921 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12921 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12921 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12921 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12921 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12921 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12921 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12921 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052028686669 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12921) ≤ 0.010506127585 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12921 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035498978924)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010506127585 + 2 * 0.737676 / 12921) := by gcongr
    _ ≤ (0.052028686669 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12921 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12921

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12921
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513391626 : ℝ) ≤ plow 12921 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12921) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533710393)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355950489) : eMP 12921 0.011 xi bn ≤ 0.001167645605 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12921 : ℝ) * (1 - 0.011))) ≤ 0.000577365285 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355950489 / (12921 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577365285 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577365285 : ℝ) + 3.141593 * 0.052533710393 / (12921 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167645605 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533710393)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355950489) : PiBarMP 12921 12 0.011 xi bn ≤ 0.159852295632 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12921 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036823233006 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.043659707212 : ℝ) ≤ √((12921 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.670576667843 : ℝ) ≤ √(12921 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12921) ≤ 0.122568290504 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036823233006 + 0.052533710393 * 1.772454 / (2 * (113.043659707212 : ℝ))) * (1 + 0.001167645605) +
        8 / (12921 * 113.670576667843) + 0.122568290504 := by gcongr
    _ ≤ (0.159852295632 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533710393)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355950489) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281231021721) :
    parallelOracle 12921 0.011 xi bn cd ≤ 0.160825759430 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12921 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12921 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513391626 : ℝ) ≤ plow 12921 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.670576667843 : ℝ) ≤ √(12921 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281231021721 : ℝ) / (2 * 0.560513391626 * 113.670576667843)) * 0.159852295632 +
        0.281231021721 ^ 2 / (2 * 0.560513391626 * 113.670576667843) := by gcongr
    _ ≤ (0.160825759430 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533710393) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355950489)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281231021721) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12921 12921 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513391626 : ℝ) ≤ plow 12921 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.670576667843 : ℝ) ≤ √(12921 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12921 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12921 Θ 1.22 ≤ 0.011666172012 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.670576667843 := by gcongr <;> linarith
      _ ≤ (0.011666172012 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12921 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12921 12921 0.011 ≤ 0.008409273484 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12921 12921 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12921 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12921 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12921 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12921 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160825759430 + 0.011666172012 + (0.008409273484 : ℝ) *
        (1 + 2 * (0.281231021721 + 0.011666172012) / (0.560513391626 * 113.670576667843))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12921]

end BstLean.Part269.N12921

/-! The original eight local profiles supply actual 12921 moment certificates. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12921 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052533710393 ∧
    0 ≤ bN 12921 BstLean.Part154.csC (groupTheta g) ∧ bN 12921 BstLean.Part154.csC (groupTheta g) ≤ 0.001355950489 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12921 12921 0.011
      (momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12921 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12921 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12921 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229202335052 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12921 0.011
      (momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12921 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12921
/-! The actual computed-centre upper energy formula at 12921. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12921

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12921)
open BstLean.Part268 (cell12921)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084870383267
  | 2 => 0.085802281644
  | 3 => 0.086730825095
  | 4 => 0.087657081539
  | 5 => 0.088582353250
  | 6 => 0.089508212984
  | 7 => 0.090436543778
  | 8 => 0.091369582462
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12921 12921 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12921 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12921

/-! Actual upper energy certificates on all 43 source endpoints at 12921. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12921)
open BstLean.Part268 (cell12921)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12921 (gMinus 12921) (1 - (cell12921 i).lower) ≤ 1 ∧
    energyUpper 12921 (gMinus 12921) (BstLean.Part211.gPlus 12921)
      (finiteEnergy 12921 12921 0.011) (1 - (cell12921 i).lower) ≤
      (cell12921 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨10,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨11,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨12,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨13,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨14,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨15,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨16,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨17,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨18,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨19,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨20,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨21,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨22,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨23,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨24,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨25,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨26,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨27,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨28,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨29,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨30,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨31,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨32,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨33,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨34,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨35,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨36,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨37,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨38,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨39,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨40,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨41,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨42,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨43,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨44,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨45,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨46,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨47,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨48,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨49,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨50,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨51,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12921) (by norm_num)
        (q := 1 - (cell12921 ⟨52,by decide⟩).lower)
        (by norm_num [cell12921]) (by norm_num [cell12921])
      exact ⟨E.1,E.2.trans (by norm_num [cell12921])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12921

/-! Source-cell containment and simple scalar guards at 12921. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12921)
open BstLean.Part268 (cell12921)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12921 ⟨10,by decide⟩).lower ∧ (cell12921 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12921 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12921 ⟨11,by decide⟩).lower ∧ (cell12921 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12921 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12921 ⟨12,by decide⟩).lower ∧ (cell12921 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12921 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12921 ⟨13,by decide⟩).lower ∧ (cell12921 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12921 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12921 ⟨14,by decide⟩).lower ∧ (cell12921 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12921 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12921 ⟨15,by decide⟩).lower ∧ (cell12921 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12921 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12921 ⟨16,by decide⟩).lower ∧ (cell12921 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12921 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12921 ⟨17,by decide⟩).lower ∧ (cell12921 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12921 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12921 ⟨18,by decide⟩).lower ∧ (cell12921 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12921 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12921 ⟨19,by decide⟩).lower ∧ (cell12921 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12921 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12921 ⟨20,by decide⟩).lower ∧ (cell12921 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12921 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12921 ⟨21,by decide⟩).lower ∧ (cell12921 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12921 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12921 ⟨22,by decide⟩).lower ∧ (cell12921 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12921 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12921 ⟨23,by decide⟩).lower ∧ (cell12921 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12921 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12921 ⟨24,by decide⟩).lower ∧ (cell12921 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12921 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12921 ⟨25,by decide⟩).lower ∧ (cell12921 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12921 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12921 ⟨26,by decide⟩).lower ∧ (cell12921 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12921 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12921 ⟨27,by decide⟩).lower ∧ (cell12921 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12921 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12921 ⟨28,by decide⟩).lower ∧ (cell12921 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12921 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12921 ⟨29,by decide⟩).lower ∧ (cell12921 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12921 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12921 ⟨30,by decide⟩).lower ∧ (cell12921 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12921 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12921 ⟨31,by decide⟩).lower ∧ (cell12921 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12921 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12921 ⟨32,by decide⟩).lower ∧ (cell12921 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12921 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12921 ⟨33,by decide⟩).lower ∧ (cell12921 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12921 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12921 ⟨34,by decide⟩).lower ∧ (cell12921 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12921 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12921 ⟨35,by decide⟩).lower ∧ (cell12921 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12921 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12921 ⟨36,by decide⟩).lower ∧ (cell12921 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12921 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12921 ⟨37,by decide⟩).lower ∧ (cell12921 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12921 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12921 ⟨38,by decide⟩).lower ∧ (cell12921 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12921 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12921 ⟨39,by decide⟩).lower ∧ (cell12921 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12921 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12921 ⟨40,by decide⟩).lower ∧ (cell12921 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12921 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12921 ⟨41,by decide⟩).lower ∧ (cell12921 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12921 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12921 ⟨42,by decide⟩).lower ∧ (cell12921 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12921 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12921 ⟨43,by decide⟩).lower ∧ (cell12921 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12921 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12921 ⟨44,by decide⟩).lower ∧ (cell12921 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12921 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12921 ⟨45,by decide⟩).lower ∧ (cell12921 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12921 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12921 ⟨46,by decide⟩).lower ∧ (cell12921 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12921 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12921 ⟨47,by decide⟩).lower ∧ (cell12921 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12921 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12921 ⟨48,by decide⟩).lower ∧ (cell12921 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12921 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12921 ⟨49,by decide⟩).lower ∧ (cell12921 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12921 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12921 ⟨50,by decide⟩).lower ∧ (cell12921 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12921 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12921 ⟨51,by decide⟩).lower ∧ (cell12921 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12921 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12921 ⟨52,by decide⟩).lower ∧ (cell12921 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12921 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12921 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12921 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12921,cell12921,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12921 i).lower ∧
    (cell12921 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12921 i).upper ≤ (0.532 : ℝ) ∧
    (cell12921 i).centre ≤ (0.1 : ℝ) ∧ (cell12921 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12921 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12921 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12921

/-! The local source numeric instances at 12921 have no network premises. -/
namespace BstLean.Part269.N12921
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12921)
open BstLean.Part268 (cell12921)

noncomputable def sourceNumerics12921 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12921 (cell12921 i)
      scalarRow12921.M scalarRow12921.H scalarRow12921.xi := by
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
    energy_allowance := scalarRow12921.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12921]
    centre_nonneg := (scalarRow12921.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12921])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12921
/-! Actual 12922 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12922 ≤ (1.035497593332 : ℝ) := by
  have hr : (113.674975258409 : ℝ) ≤ √(12922 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.674975258409 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12922 12922 (11 / 1000) ≤
    (0.008408948089 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12922) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.674975258409 : ℝ) ≤ √(12922 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12922)
  have hdiv : K / √(12922 : ℝ) ≤ K / 113.674975258409 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.674975258409 ≤ (0.008408948089 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12922.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12922 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12922 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12922 := gPlus_lower 12922
end BstLean.Part269.N12922

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12922
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035497593331 : ℝ) ≤ wn 12922 := by
  have hn : √(12922 : ℝ) ≤ 113.674975258410 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12922 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.674975258410 ≤ 2 / √(12922 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247479077 : ℝ) ≤ rhoBar 12922 BstLean.Part154.csC ∧
    rhoBar 12922 BstLean.Part154.csC ≤ 0.000247479460 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035497593331 : ℝ) / (1.295212 * 12922) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035497593332 : ℝ) / (1.29521 * 12922) := by gcongr
      _ ≤ (0.000247479460 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12922 BstLean.Part154.csC) ≤ 0.000989979087 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12922 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) ≤ 0.000189026327 ∧
    cc1 (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) ≤ 0.000120278739 ∧
    cc2 (rhoBar 12922 BstLean.Part154.csC) ≤ 0.000069822768 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12922 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12922 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12922 BstLean.Part154.csC * nuR (rhoBar 12922 BstLean.Part154.csC)) ≤ 0.000494974232 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247479460 : ℝ) * 0.000989979087 := by gcongr
      _ ≤ (0.000494974232 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12922 BstLean.Part154.csC) * nuR (rhoBar 12922 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989979087 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12922 BstLean.Part154.csC) * rhoBar 12922 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247479460 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247479460 / 2 + 0.399 * 0.000989979087 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189026327 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494974232 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120278739 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247479460 / 1.414213562 := by gcongr
      _ ≤ (0.000069822768 : ℝ) := by norm_num

end BstLean.Part269.N12922

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12922
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) ≤ 1.54305E-7 := by
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12922 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12922 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12922 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189026327 : ℝ) ^ 2 + 0.000120278739 ^ 2 + 3 * 0.000069822768 ^ 2 +
        2 * 0.797885 * 0.000189026327 * 0.000120278739 + 2 * 0.000189026327 * 0.000069822768 +
        4 * 0.797885 * 0.000120278739 * 0.000069822768 := by gcongr
    _ ≤ (1.54305E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12922 BstLean.Part154.csC Θ ≤ 0.002582561049 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12922 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12922 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12922 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035497593332 * 1.54305E-7 / (0.000247479077 : ℝ) := by gcongr
    _ ≤ 0.002582561049 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12922 BstLean.Part154.csC Θ ≤ 0.002864627908 + 0.000652572035 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12922 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12922 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035497593332 : ℝ) * ((2 * Θ * 0.000247479460 +
        (6863 / 10000) * 0.000247479460 * 12922 * 0.000989979087) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002864627908 + 0.000652572035 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12922 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12922 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12922 0.011 Θ ∧ gammaRatio 12922 0.011 Θ ≤ 0.000085077039 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12922 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035497593332 : ℝ) * 0.525 / ((1 - 0.011) * 12922) := by gcongr
      _ ≤ (0.000085077039 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12922 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12922 0.011 Θ) :=
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
    badAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12922 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12922 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12922 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12922 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12922 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12922 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12922 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12922 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12922 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12922 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035497593332 : ℝ) * 12922 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003328298925 + 0.003235133084 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12922

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12922
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12922 BstLean.Part154.csC) (piBar (rhoBar 12922 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12922 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12922 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12922 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12922 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12922 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12922 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12922 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12922 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12922 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12922 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052026651803 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12922) ≤ 0.010505721056 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12922 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035497593332)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010505721056 + 2 * 0.737676 / 12922) := by gcongr
    _ ≤ (0.052026651803 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12922 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12922

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12922
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513435311 : ℝ) ≤ plow 12922 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12922) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533343795)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355844551) : eMP 12922 0.011 xi bn ≤ 0.001167554726 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12922 : ℝ) * (1 - 0.011))) ≤ 0.000577320390 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355844551 / (12922 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577320390 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577320390 : ℝ) + 3.141593 * 0.052533343795 / (12922 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167554726 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533343795)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355844551) : PiBarMP 12922 12 0.011 xi bn ≤ 0.159846089898 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12922 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036821794511 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.048034038633 : ℝ) ≤ √((12922 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.674975258409 : ℝ) ≤ √(12922 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12922) ≤ 0.122563547792 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036821794511 + 0.052533343795 * 1.772454 / (2 * (113.048034038633 : ℝ))) * (1 + 0.001167554726) +
        8 / (12922 * 113.674975258409) + 0.122563547792 := by gcongr
    _ ≤ (0.159846089898 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533343795)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355844551) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281228187128) :
    parallelOracle 12922 0.011 xi bn cd ≤ 0.160819486190 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12922 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12922 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513435311 : ℝ) ≤ plow 12922 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.674975258409 : ℝ) ≤ √(12922 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281228187128 : ℝ) / (2 * 0.560513435311 * 113.674975258409)) * 0.159846089898 +
        0.281228187128 ^ 2 / (2 * 0.560513435311 * 113.674975258409) := by gcongr
    _ ≤ (0.160819486190 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052533343795) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355844551)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281228187128) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12922 12922 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513435311 : ℝ) ≤ plow 12922 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.674975258409 : ℝ) ≤ √(12922 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12922 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12922 Θ 1.22 ≤ 0.011665720595 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.674975258409 := by gcongr <;> linarith
      _ ≤ (0.011665720595 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12922 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12922 12922 0.011 ≤ 0.008408948089 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12922 12922 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12922 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12922 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12922 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12922 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160819486190 + 0.011665720595 + (0.008408948089 : ℝ) *
        (1 + 2 * (0.281228187128 + 0.011665720595) / (0.560513435311 * 113.674975258409))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12922]

end BstLean.Part269.N12922

/-! The original eight local profiles supply actual 12922 moment certificates. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12922 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052533343795 ∧
    0 ≤ bN 12922 BstLean.Part154.csC (groupTheta g) ∧ bN 12922 BstLean.Part154.csC (groupTheta g) ≤ 0.001355844551 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12922 12922 0.011
      (momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12922 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12922 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12922 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229201535325 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12922 0.011
      (momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12922 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12922
/-! The actual computed-centre upper energy formula at 12922. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12922

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12922)
open BstLean.Part268 (cell12922)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084867682519
  | 2 => 0.085799535888
  | 3 => 0.086728028530
  | 4 => 0.087654226981
  | 5 => 0.088579431874
  | 6 => 0.089505214046
  | 7 => 0.090433454286
  | 8 => 0.091366386824
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12922 12922 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12922 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12922

/-! Actual upper energy certificates on all 43 source endpoints at 12922. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12922)
open BstLean.Part268 (cell12922)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12922 (gMinus 12922) (1 - (cell12922 i).lower) ≤ 1 ∧
    energyUpper 12922 (gMinus 12922) (BstLean.Part211.gPlus 12922)
      (finiteEnergy 12922 12922 0.011) (1 - (cell12922 i).lower) ≤
      (cell12922 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨10,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨11,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨12,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨13,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨14,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨15,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨16,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨17,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨18,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨19,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨20,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨21,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨22,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨23,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨24,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨25,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨26,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨27,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨28,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨29,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨30,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨31,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨32,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨33,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨34,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨35,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨36,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨37,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨38,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨39,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨40,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨41,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨42,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨43,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨44,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨45,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨46,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨47,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨48,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨49,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨50,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨51,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12922) (by norm_num)
        (q := 1 - (cell12922 ⟨52,by decide⟩).lower)
        (by norm_num [cell12922]) (by norm_num [cell12922])
      exact ⟨E.1,E.2.trans (by norm_num [cell12922])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12922

/-! Source-cell containment and simple scalar guards at 12922. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12922)
open BstLean.Part268 (cell12922)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12922 ⟨10,by decide⟩).lower ∧ (cell12922 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12922 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12922 ⟨11,by decide⟩).lower ∧ (cell12922 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12922 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12922 ⟨12,by decide⟩).lower ∧ (cell12922 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12922 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12922 ⟨13,by decide⟩).lower ∧ (cell12922 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12922 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12922 ⟨14,by decide⟩).lower ∧ (cell12922 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12922 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12922 ⟨15,by decide⟩).lower ∧ (cell12922 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12922 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12922 ⟨16,by decide⟩).lower ∧ (cell12922 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12922 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12922 ⟨17,by decide⟩).lower ∧ (cell12922 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12922 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12922 ⟨18,by decide⟩).lower ∧ (cell12922 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12922 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12922 ⟨19,by decide⟩).lower ∧ (cell12922 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12922 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12922 ⟨20,by decide⟩).lower ∧ (cell12922 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12922 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12922 ⟨21,by decide⟩).lower ∧ (cell12922 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12922 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12922 ⟨22,by decide⟩).lower ∧ (cell12922 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12922 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12922 ⟨23,by decide⟩).lower ∧ (cell12922 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12922 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12922 ⟨24,by decide⟩).lower ∧ (cell12922 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12922 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12922 ⟨25,by decide⟩).lower ∧ (cell12922 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12922 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12922 ⟨26,by decide⟩).lower ∧ (cell12922 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12922 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12922 ⟨27,by decide⟩).lower ∧ (cell12922 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12922 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12922 ⟨28,by decide⟩).lower ∧ (cell12922 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12922 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12922 ⟨29,by decide⟩).lower ∧ (cell12922 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12922 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12922 ⟨30,by decide⟩).lower ∧ (cell12922 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12922 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12922 ⟨31,by decide⟩).lower ∧ (cell12922 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12922 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12922 ⟨32,by decide⟩).lower ∧ (cell12922 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12922 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12922 ⟨33,by decide⟩).lower ∧ (cell12922 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12922 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12922 ⟨34,by decide⟩).lower ∧ (cell12922 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12922 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12922 ⟨35,by decide⟩).lower ∧ (cell12922 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12922 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12922 ⟨36,by decide⟩).lower ∧ (cell12922 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12922 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12922 ⟨37,by decide⟩).lower ∧ (cell12922 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12922 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12922 ⟨38,by decide⟩).lower ∧ (cell12922 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12922 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12922 ⟨39,by decide⟩).lower ∧ (cell12922 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12922 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12922 ⟨40,by decide⟩).lower ∧ (cell12922 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12922 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12922 ⟨41,by decide⟩).lower ∧ (cell12922 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12922 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12922 ⟨42,by decide⟩).lower ∧ (cell12922 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12922 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12922 ⟨43,by decide⟩).lower ∧ (cell12922 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12922 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12922 ⟨44,by decide⟩).lower ∧ (cell12922 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12922 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12922 ⟨45,by decide⟩).lower ∧ (cell12922 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12922 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12922 ⟨46,by decide⟩).lower ∧ (cell12922 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12922 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12922 ⟨47,by decide⟩).lower ∧ (cell12922 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12922 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12922 ⟨48,by decide⟩).lower ∧ (cell12922 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12922 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12922 ⟨49,by decide⟩).lower ∧ (cell12922 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12922 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12922 ⟨50,by decide⟩).lower ∧ (cell12922 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12922 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12922 ⟨51,by decide⟩).lower ∧ (cell12922 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12922 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12922 ⟨52,by decide⟩).lower ∧ (cell12922 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12922 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12922 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12922 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12922,cell12922,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12922 i).lower ∧
    (cell12922 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12922 i).upper ≤ (0.532 : ℝ) ∧
    (cell12922 i).centre ≤ (0.1 : ℝ) ∧ (cell12922 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12922 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12922 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12922

/-! The local source numeric instances at 12922 have no network premises. -/
namespace BstLean.Part269.N12922
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12922)
open BstLean.Part268 (cell12922)

noncomputable def sourceNumerics12922 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12922 (cell12922 i)
      scalarRow12922.M scalarRow12922.H scalarRow12922.xi := by
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
    energy_allowance := scalarRow12922.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12922]
    centre_nonneg := (scalarRow12922.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12922])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12922
/-! Actual 12923 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12923 ≤ (1.035496207902 : ℝ) := by
  have hr : (113.679373678781 : ℝ) ≤ √(12923 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.679373678781 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12923 12923 (11 / 1000) ≤
    (0.008408622732 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12923) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.679373678781 : ℝ) ≤ √(12923 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12923)
  have hdiv : K / √(12923 : ℝ) ≤ K / 113.679373678781 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.679373678781 ≤ (0.008408622732 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12923.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12923 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12923 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12923 := gPlus_lower 12923
end BstLean.Part269.N12923

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12923
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035496207901 : ℝ) ≤ wn 12923 := by
  have hn : √(12923 : ℝ) ≤ 113.679373678782 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12923 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.679373678782 ≤ 2 / √(12923 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247459596 : ℝ) ≤ rhoBar 12923 BstLean.Part154.csC ∧
    rhoBar 12923 BstLean.Part154.csC ≤ 0.000247459979 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035496207901 : ℝ) / (1.295212 * 12923) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035496207902 : ℝ) / (1.29521 * 12923) := by gcongr
      _ ≤ (0.000247459979 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12923 BstLean.Part154.csC) ≤ 0.000989901153 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12923 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) ≤ 0.000189011447 ∧
    cc1 (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) ≤ 0.000120269271 ∧
    cc2 (rhoBar 12923 BstLean.Part154.csC) ≤ 0.000069817272 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12923 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12923 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12923 BstLean.Part154.csC * nuR (rhoBar 12923 BstLean.Part154.csC)) ≤ 0.000494935268 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247459979 : ℝ) * 0.000989901153 := by gcongr
      _ ≤ (0.000494935268 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12923 BstLean.Part154.csC) * nuR (rhoBar 12923 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989901153 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12923 BstLean.Part154.csC) * rhoBar 12923 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247459979 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247459979 / 2 + 0.399 * 0.000989901153 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189011447 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494935268 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120269271 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247459979 / 1.414213562 := by gcongr
      _ ≤ (0.000069817272 : ℝ) := by norm_num

end BstLean.Part269.N12923

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12923
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) ≤ 1.54281E-7 := by
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12923 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12923 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12923 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189011447 : ℝ) ^ 2 + 0.000120269271 ^ 2 + 3 * 0.000069817272 ^ 2 +
        2 * 0.797885 * 0.000189011447 * 0.000120269271 + 2 * 0.000189011447 * 0.000069817272 +
        4 * 0.797885 * 0.000120269271 * 0.000069817272 := by gcongr
    _ ≤ (1.54281E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12923 BstLean.Part154.csC Θ ≤ 0.002582359190 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12923 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12923 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12923 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035496207902 * 1.54281E-7 / (0.000247459596 : ℝ) := by gcongr
    _ ≤ 0.002582359190 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12923 BstLean.Part154.csC Θ ≤ 0.002864394736 + 0.000652519793 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12923 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12923 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035496207902 : ℝ) * ((2 * Θ * 0.000247459979 +
        (6863 / 10000) * 0.000247459979 * 12923 * 0.000989901153) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002864394736 + 0.000652519793 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12923 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12923 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12923 0.011 Θ ∧ gammaRatio 12923 0.011 Θ ≤ 0.000085070342 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12923 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035496207902 : ℝ) * 0.525 / ((1 - 0.011) * 12923) := by gcongr
      _ ≤ (0.000085070342 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12923 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12923 0.011 Θ) :=
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
    badAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12923 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12923 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12923 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12923 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12923 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12923 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12923 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12923 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12923 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12923 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035496207902 : ℝ) * 12923 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003328065753 + 0.003234878983 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12923

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12923
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12923 BstLean.Part154.csC) (piBar (rhoBar 12923 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12923 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12923 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12923 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12923 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12923 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12923 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12923 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12923 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12923 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12923 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052024617174 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12923) ≤ 0.010505314574 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12923 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035496207902)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010505314574 + 2 * 0.737676 / 12923) := by gcongr
    _ ≤ (0.052024617174 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12923 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12923

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12923
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513478990 : ℝ) ≤ plow 12923 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12923) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532977220)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355738575) : eMP 12923 0.011 xi bn ≤ 0.001167463838 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12923 : ℝ) * (1 - 0.011))) ≤ 0.000577275491 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355738575 / (12923 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577275491 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577275491 : ℝ) + 3.141593 * 0.052532977220 / (12923 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167463838 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532977220)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355738575) : PiBarMP 12923 12 0.011 xi bn ≤ 0.159839884142 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12923 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036820355444 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.052408200798 : ℝ) ≤ √((12923 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.679373678781 : ℝ) ≤ √(12923 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12923) ≤ 0.122558805630 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036820355444 + 0.052532977220 * 1.772454 / (2 * (113.052408200798 : ℝ))) * (1 + 0.001167463838) +
        8 / (12923 * 113.679373678781) + 0.122558805630 := by gcongr
    _ ≤ (0.159839884142 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532977220)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355738575) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281225352819) :
    parallelOracle 12923 0.011 xi bn cd ≤ 0.160813212937 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12923 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12923 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513478990 : ℝ) ≤ plow 12923 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.679373678781 : ℝ) ≤ √(12923 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281225352819 : ℝ) / (2 * 0.560513478990 * 113.679373678781)) * 0.159839884142 +
        0.281225352819 ^ 2 / (2 * 0.560513478990 * 113.679373678781) := by gcongr
    _ ≤ (0.160813212937 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532977220) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355738575)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281225352819) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12923 12923 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513478990 : ℝ) ≤ plow 12923 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.679373678781 : ℝ) ≤ √(12923 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12923 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12923 Θ 1.22 ≤ 0.011665269232 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.679373678781 := by gcongr <;> linarith
      _ ≤ (0.011665269232 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12923 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12923 12923 0.011 ≤ 0.008408622732 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12923 12923 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12923 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12923 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12923 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12923 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160813212937 + 0.011665269232 + (0.008408622732 : ℝ) *
        (1 + 2 * (0.281225352819 + 0.011665269232) / (0.560513478990 * 113.679373678781))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12923]

end BstLean.Part269.N12923

/-! The original eight local profiles supply actual 12923 moment certificates. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12923 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052532977220 ∧
    0 ≤ bN 12923 BstLean.Part154.csC (groupTheta g) ∧ bN 12923 BstLean.Part154.csC (groupTheta g) ≤ 0.001355738575 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12923 12923 0.011
      (momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12923 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12923 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12923 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229200735645 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12923 0.011
      (momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12923 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12923
/-! The actual computed-centre upper energy formula at 12923. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12923

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12923)
open BstLean.Part268 (cell12923)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084864982643
  | 2 => 0.085796791037
  | 3 => 0.086725232912
  | 4 => 0.087651373420
  | 5 => 0.088576511559
  | 6 => 0.089502216244
  | 7 => 0.090430366022
  | 8 => 0.091363192523
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12923 12923 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12923 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12923

/-! Actual upper energy certificates on all 43 source endpoints at 12923. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12923)
open BstLean.Part268 (cell12923)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12923 (gMinus 12923) (1 - (cell12923 i).lower) ≤ 1 ∧
    energyUpper 12923 (gMinus 12923) (BstLean.Part211.gPlus 12923)
      (finiteEnergy 12923 12923 0.011) (1 - (cell12923 i).lower) ≤
      (cell12923 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨10,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨11,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨12,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨13,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨14,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨15,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨16,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨17,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨18,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨19,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨20,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨21,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨22,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨23,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨24,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨25,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨26,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨27,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨28,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨29,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨30,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨31,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨32,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨33,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨34,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨35,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨36,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨37,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨38,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨39,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨40,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨41,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨42,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨43,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨44,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨45,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨46,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨47,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨48,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨49,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨50,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨51,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12923) (by norm_num)
        (q := 1 - (cell12923 ⟨52,by decide⟩).lower)
        (by norm_num [cell12923]) (by norm_num [cell12923])
      exact ⟨E.1,E.2.trans (by norm_num [cell12923])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12923

/-! Source-cell containment and simple scalar guards at 12923. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12923)
open BstLean.Part268 (cell12923)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12923 ⟨10,by decide⟩).lower ∧ (cell12923 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12923 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12923 ⟨11,by decide⟩).lower ∧ (cell12923 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12923 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12923 ⟨12,by decide⟩).lower ∧ (cell12923 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12923 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12923 ⟨13,by decide⟩).lower ∧ (cell12923 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12923 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12923 ⟨14,by decide⟩).lower ∧ (cell12923 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12923 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12923 ⟨15,by decide⟩).lower ∧ (cell12923 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12923 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12923 ⟨16,by decide⟩).lower ∧ (cell12923 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12923 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12923 ⟨17,by decide⟩).lower ∧ (cell12923 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12923 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12923 ⟨18,by decide⟩).lower ∧ (cell12923 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12923 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12923 ⟨19,by decide⟩).lower ∧ (cell12923 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12923 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12923 ⟨20,by decide⟩).lower ∧ (cell12923 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12923 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12923 ⟨21,by decide⟩).lower ∧ (cell12923 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12923 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12923 ⟨22,by decide⟩).lower ∧ (cell12923 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12923 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12923 ⟨23,by decide⟩).lower ∧ (cell12923 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12923 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12923 ⟨24,by decide⟩).lower ∧ (cell12923 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12923 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12923 ⟨25,by decide⟩).lower ∧ (cell12923 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12923 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12923 ⟨26,by decide⟩).lower ∧ (cell12923 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12923 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12923 ⟨27,by decide⟩).lower ∧ (cell12923 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12923 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12923 ⟨28,by decide⟩).lower ∧ (cell12923 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12923 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12923 ⟨29,by decide⟩).lower ∧ (cell12923 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12923 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12923 ⟨30,by decide⟩).lower ∧ (cell12923 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12923 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12923 ⟨31,by decide⟩).lower ∧ (cell12923 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12923 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12923 ⟨32,by decide⟩).lower ∧ (cell12923 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12923 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12923 ⟨33,by decide⟩).lower ∧ (cell12923 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12923 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12923 ⟨34,by decide⟩).lower ∧ (cell12923 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12923 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12923 ⟨35,by decide⟩).lower ∧ (cell12923 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12923 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12923 ⟨36,by decide⟩).lower ∧ (cell12923 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12923 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12923 ⟨37,by decide⟩).lower ∧ (cell12923 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12923 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12923 ⟨38,by decide⟩).lower ∧ (cell12923 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12923 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12923 ⟨39,by decide⟩).lower ∧ (cell12923 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12923 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12923 ⟨40,by decide⟩).lower ∧ (cell12923 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12923 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12923 ⟨41,by decide⟩).lower ∧ (cell12923 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12923 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12923 ⟨42,by decide⟩).lower ∧ (cell12923 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12923 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12923 ⟨43,by decide⟩).lower ∧ (cell12923 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12923 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12923 ⟨44,by decide⟩).lower ∧ (cell12923 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12923 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12923 ⟨45,by decide⟩).lower ∧ (cell12923 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12923 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12923 ⟨46,by decide⟩).lower ∧ (cell12923 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12923 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12923 ⟨47,by decide⟩).lower ∧ (cell12923 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12923 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12923 ⟨48,by decide⟩).lower ∧ (cell12923 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12923 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12923 ⟨49,by decide⟩).lower ∧ (cell12923 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12923 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12923 ⟨50,by decide⟩).lower ∧ (cell12923 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12923 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12923 ⟨51,by decide⟩).lower ∧ (cell12923 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12923 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12923 ⟨52,by decide⟩).lower ∧ (cell12923 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12923 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12923 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12923 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12923,cell12923,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12923 i).lower ∧
    (cell12923 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12923 i).upper ≤ (0.532 : ℝ) ∧
    (cell12923 i).centre ≤ (0.1 : ℝ) ∧ (cell12923 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12923 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12923 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12923

/-! The local source numeric instances at 12923 have no network premises. -/
namespace BstLean.Part269.N12923
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12923)
open BstLean.Part268 (cell12923)

noncomputable def sourceNumerics12923 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12923 (cell12923 i)
      scalarRow12923.M scalarRow12923.H scalarRow12923.xi := by
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
    energy_allowance := scalarRow12923.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12923]
    centre_nonneg := (scalarRow12923.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12923])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12923
/-! Actual 12924 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12924 ≤ (1.035494822634 : ℝ) := by
  have hr : (113.683771928978 : ℝ) ≤ √(12924 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.683771928978 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12924 12924 (11 / 1000) ≤
    (0.008408297413 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12924) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.683771928978 : ℝ) ≤ √(12924 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12924)
  have hdiv : K / √(12924 : ℝ) ≤ K / 113.683771928978 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.683771928978 ≤ (0.008408297413 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12924.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12924 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12924 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12924 := gPlus_lower 12924
end BstLean.Part269.N12924

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12924
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035494822633 : ℝ) ≤ wn 12924 := by
  have hn : √(12924 : ℝ) ≤ 113.683771928979 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12924 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.683771928979 ≤ 2 / √(12924 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247440118 : ℝ) ≤ rhoBar 12924 BstLean.Part154.csC ∧
    rhoBar 12924 BstLean.Part154.csC ≤ 0.000247440501 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035494822633 : ℝ) / (1.295212 * 12924) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035494822634 : ℝ) / (1.29521 * 12924) := by gcongr
      _ ≤ (0.000247440501 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12924 BstLean.Part154.csC) ≤ 0.000989823231 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12924 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) ≤ 0.000188996569 ∧
    cc1 (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) ≤ 0.000120259804 ∧
    cc2 (rhoBar 12924 BstLean.Part154.csC) ≤ 0.000069811776 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12924 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12924 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12924 BstLean.Part154.csC * nuR (rhoBar 12924 BstLean.Part154.csC)) ≤ 0.000494896309 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247440501 : ℝ) * 0.000989823231 := by gcongr
      _ ≤ (0.000494896309 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12924 BstLean.Part154.csC) * nuR (rhoBar 12924 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989823231 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12924 BstLean.Part154.csC) * rhoBar 12924 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247440501 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247440501 / 2 + 0.399 * 0.000989823231 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188996569 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494896309 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120259804 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247440501 / 1.414213562 := by gcongr
      _ ≤ (0.000069811776 : ℝ) := by norm_num

end BstLean.Part269.N12924

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12924
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) ≤ 1.54257E-7 := by
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12924 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12924 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12924 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188996569 : ℝ) ^ 2 + 0.000120259804 ^ 2 + 3 * 0.000069811776 ^ 2 +
        2 * 0.797885 * 0.000188996569 * 0.000120259804 + 2 * 0.000188996569 * 0.000069811776 +
        4 * 0.797885 * 0.000120259804 * 0.000069811776 := by gcongr
    _ ≤ (1.54257E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12924 BstLean.Part154.csC Θ ≤ 0.002582157270 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12924 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12924 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12924 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035494822634 * 1.54257E-7 / (0.000247440118 : ℝ) := by gcongr
    _ ≤ 0.002582157270 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12924 BstLean.Part154.csC Θ ≤ 0.002864161600 + 0.000652467559 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12924 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12924 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035494822634 : ℝ) * ((2 * Θ * 0.000247440501 +
        (6863 / 10000) * 0.000247440501 * 12924 * 0.000989823231) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002864161600 + 0.000652467559 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12924 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12924 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12924 0.011 Θ ∧ gammaRatio 12924 0.011 Θ ≤ 0.000085063646 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12924 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035494822634 : ℝ) * 0.525 / ((1 - 0.011) * 12924) := by gcongr
      _ ≤ (0.000085063646 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12924 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12924 0.011 Θ) :=
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
    badAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12924 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12924 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12924 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12924 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12924 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12924 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12924 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12924 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12924 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12924 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035494822634 : ℝ) * 12924 *
        (1.6832E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003327832617 + 0.003234624829 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12924

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12924
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12924 BstLean.Part154.csC) (piBar (rhoBar 12924 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12924 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12924 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12924 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12924 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12924 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12924 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12924 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12924 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12924 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12924 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052022582786 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12924) ≤ 0.010504908140 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12924 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035494822634)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010504908140 + 2 * 0.737676 / 12924) := by gcongr
    _ ≤ (0.052022582786 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12924 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12924

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12924
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513522663 : ℝ) ≤ plow 12924 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12924) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532610653)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355632567) : eMP 12924 0.011 xi bn ≤ 0.001167372943 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12924 : ℝ) * (1 - 0.011))) ≤ 0.000577230588 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355632567 / (12924 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577230588 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577230588 : ℝ) + 3.141593 * 0.052532610653 / (12924 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167372943 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532610653)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355632567) : PiBarMP 12924 12 0.011 xi bn ≤ 0.159833678448 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12924 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036818915886 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.056782193727 : ℝ) ≤ √((12924 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.683771928978 : ℝ) ≤ √(12924 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12924) ≤ 0.122554064018 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036818915886 + 0.052532610653 * 1.772454 / (2 * (113.056782193727 : ℝ))) * (1 + 0.001167372943) +
        8 / (12924 * 113.683771928978) + 0.122554064018 := by gcongr
    _ ≤ (0.159833678448 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532610653)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355632567) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281222518766) :
    parallelOracle 12924 0.011 xi bn cd ≤ 0.160806939754 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12924 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12924 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513522663 : ℝ) ≤ plow 12924 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.683771928978 : ℝ) ≤ √(12924 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281222518766 : ℝ) / (2 * 0.560513522663 * 113.683771928978)) * 0.159833678448 +
        0.281222518766 ^ 2 / (2 * 0.560513522663 * 113.683771928978) := by gcongr
    _ ≤ (0.160806939754 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052532610653) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355632567)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281222518766) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12924 12924 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513522663 : ℝ) ≤ plow 12924 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.683771928978 : ℝ) ≤ √(12924 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12924 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12924 Θ 1.22 ≤ 0.011664817920 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.683771928978 := by gcongr <;> linarith
      _ ≤ (0.011664817920 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12924 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12924 12924 0.011 ≤ 0.008408297413 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12924 12924 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12924 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12924 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12924 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12924 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160806939754 + 0.011664817920 + (0.008408297413 : ℝ) *
        (1 + 2 * (0.281222518766 + 0.011664817920) / (0.560513522663 * 113.683771928978))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12924]

end BstLean.Part269.N12924

/-! The original eight local profiles supply actual 12924 moment certificates. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12924 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052532610653 ∧
    0 ≤ bN 12924 BstLean.Part154.csC (groupTheta g) ∧ bN 12924 BstLean.Part154.csC (groupTheta g) ≤ 0.001355632567 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12924 12924 0.011
      (momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12924 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12924 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12924 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229199935980 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12924 0.011
      (momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12924 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12924
/-! The actual computed-centre upper energy formula at 12924. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12924

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12924)
open BstLean.Part268 (cell12924)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084862283637
  | 2 => 0.085794047090
  | 3 => 0.086722438239
  | 4 => 0.087648520855
  | 5 => 0.088573592302
  | 6 => 0.089499219575
  | 7 => 0.090427278984
  | 8 => 0.091359999560
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12924 12924 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12924 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12924

/-! Actual upper energy certificates on all 43 source endpoints at 12924. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12924)
open BstLean.Part268 (cell12924)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12924 (gMinus 12924) (1 - (cell12924 i).lower) ≤ 1 ∧
    energyUpper 12924 (gMinus 12924) (BstLean.Part211.gPlus 12924)
      (finiteEnergy 12924 12924 0.011) (1 - (cell12924 i).lower) ≤
      (cell12924 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨10,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨11,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨12,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨13,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨14,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨15,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨16,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨17,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨18,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨19,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨20,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨21,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨22,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨23,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨24,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨25,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨26,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨27,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨28,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨29,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨30,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨31,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨32,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨33,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨34,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨35,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨36,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨37,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨38,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨39,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨40,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨41,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨42,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨43,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨44,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨45,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨46,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨47,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨48,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨49,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨50,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨51,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12924) (by norm_num)
        (q := 1 - (cell12924 ⟨52,by decide⟩).lower)
        (by norm_num [cell12924]) (by norm_num [cell12924])
      exact ⟨E.1,E.2.trans (by norm_num [cell12924])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12924

/-! Source-cell containment and simple scalar guards at 12924. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12924)
open BstLean.Part268 (cell12924)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12924 ⟨10,by decide⟩).lower ∧ (cell12924 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12924 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12924 ⟨11,by decide⟩).lower ∧ (cell12924 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12924 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12924 ⟨12,by decide⟩).lower ∧ (cell12924 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12924 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12924 ⟨13,by decide⟩).lower ∧ (cell12924 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12924 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12924 ⟨14,by decide⟩).lower ∧ (cell12924 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12924 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12924 ⟨15,by decide⟩).lower ∧ (cell12924 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12924 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12924 ⟨16,by decide⟩).lower ∧ (cell12924 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12924 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12924 ⟨17,by decide⟩).lower ∧ (cell12924 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12924 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12924 ⟨18,by decide⟩).lower ∧ (cell12924 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12924 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12924 ⟨19,by decide⟩).lower ∧ (cell12924 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12924 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12924 ⟨20,by decide⟩).lower ∧ (cell12924 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12924 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12924 ⟨21,by decide⟩).lower ∧ (cell12924 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12924 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12924 ⟨22,by decide⟩).lower ∧ (cell12924 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12924 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12924 ⟨23,by decide⟩).lower ∧ (cell12924 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12924 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12924 ⟨24,by decide⟩).lower ∧ (cell12924 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12924 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12924 ⟨25,by decide⟩).lower ∧ (cell12924 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12924 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12924 ⟨26,by decide⟩).lower ∧ (cell12924 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12924 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12924 ⟨27,by decide⟩).lower ∧ (cell12924 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12924 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12924 ⟨28,by decide⟩).lower ∧ (cell12924 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12924 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12924 ⟨29,by decide⟩).lower ∧ (cell12924 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12924 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12924 ⟨30,by decide⟩).lower ∧ (cell12924 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12924 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12924 ⟨31,by decide⟩).lower ∧ (cell12924 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12924 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12924 ⟨32,by decide⟩).lower ∧ (cell12924 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12924 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12924 ⟨33,by decide⟩).lower ∧ (cell12924 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12924 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12924 ⟨34,by decide⟩).lower ∧ (cell12924 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12924 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12924 ⟨35,by decide⟩).lower ∧ (cell12924 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12924 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12924 ⟨36,by decide⟩).lower ∧ (cell12924 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12924 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12924 ⟨37,by decide⟩).lower ∧ (cell12924 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12924 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12924 ⟨38,by decide⟩).lower ∧ (cell12924 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12924 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12924 ⟨39,by decide⟩).lower ∧ (cell12924 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12924 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12924 ⟨40,by decide⟩).lower ∧ (cell12924 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12924 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12924 ⟨41,by decide⟩).lower ∧ (cell12924 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12924 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12924 ⟨42,by decide⟩).lower ∧ (cell12924 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12924 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12924 ⟨43,by decide⟩).lower ∧ (cell12924 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12924 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12924 ⟨44,by decide⟩).lower ∧ (cell12924 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12924 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12924 ⟨45,by decide⟩).lower ∧ (cell12924 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12924 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12924 ⟨46,by decide⟩).lower ∧ (cell12924 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12924 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12924 ⟨47,by decide⟩).lower ∧ (cell12924 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12924 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12924 ⟨48,by decide⟩).lower ∧ (cell12924 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12924 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12924 ⟨49,by decide⟩).lower ∧ (cell12924 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12924 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12924 ⟨50,by decide⟩).lower ∧ (cell12924 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12924 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12924 ⟨51,by decide⟩).lower ∧ (cell12924 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12924 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12924 ⟨52,by decide⟩).lower ∧ (cell12924 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12924 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12924 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12924 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12924,cell12924,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12924 i).lower ∧
    (cell12924 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12924 i).upper ≤ (0.532 : ℝ) ∧
    (cell12924 i).centre ≤ (0.1 : ℝ) ∧ (cell12924 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12924 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12924 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12924

/-! The local source numeric instances at 12924 have no network premises. -/
namespace BstLean.Part269.N12924
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12924)
open BstLean.Part268 (cell12924)

noncomputable def sourceNumerics12924 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12924 (cell12924 i)
      scalarRow12924.M scalarRow12924.H scalarRow12924.xi := by
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
    energy_allowance := scalarRow12924.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12924]
    centre_nonneg := (scalarRow12924.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12924])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12924