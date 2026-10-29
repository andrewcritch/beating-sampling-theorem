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
import BstLean.Part269Direction26
import BstLean.Part269Shared26
import BstLean.Part269Finite
import BstLean.Part269Rows26
import BstLean.Part269Source
/-! Actual 13000 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13000 ≤ (1.035390013080 : ℝ) := by
  have hr : (114.017542509913 : ℝ) ≤ √(13000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.017542509913 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13000 13000 (11 / 1000) ≤
    (0.008383683101 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13000) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.017542509913 : ℝ) ≤ √(13000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13000)
  have hdiv : K / √(13000 : ℝ) ≤ K / 114.017542509913 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.017542509913 ≤ (0.008383683101 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13000.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13000 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13000 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13000 := gPlus_lower 13000
end BstLean.Part269.N13000

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13000
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035390013079 : ℝ) ≤ wn 13000 := by
  have hn : √(13000 : ℝ) ≤ 114.017542509914 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13000 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.017542509914 ≤ 2 / √(13000 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245968646 : ℝ) ≤ rhoBar 13000 BstLean.Part154.csC ∧
    rhoBar 13000 BstLean.Part154.csC ≤ 0.000245969027 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035390013079 : ℝ) / (1.295212 * 13000) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035390013080 : ℝ) / (1.29521 * 13000) := by gcongr
      _ ≤ (0.000245969027 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13000 BstLean.Part154.csC) ≤ 0.000983936609 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13000 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) ≤ 0.000187872597 ∧
    cc1 (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) ≤ 0.000119544623 ∧
    cc2 (rhoBar 13000 BstLean.Part154.csC) ≤ 0.000069396621 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13000 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13000 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13000 BstLean.Part154.csC * nuR (rhoBar 13000 BstLean.Part154.csC)) ≤ 0.000491953180 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245969027 : ℝ) * 0.000983936609 := by gcongr
      _ ≤ (0.000491953180 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13000 BstLean.Part154.csC) * nuR (rhoBar 13000 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983936609 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13000 BstLean.Part154.csC) * rhoBar 13000 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245969027 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245969027 / 2 + 0.399 * 0.000983936609 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187872597 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491953180 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119544623 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245969027 / 1.414213562 := by gcongr
      _ ≤ (0.000069396621 : ℝ) := by norm_num

end BstLean.Part269.N13000

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13000
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) ≤ 1.52427E-7 := by
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13000 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13000 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13000 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187872597 : ℝ) ^ 2 + 0.000119544623 ^ 2 + 3 * 0.000069396621 ^ 2 +
        2 * 0.797885 * 0.000187872597 * 0.000119544623 + 2 * 0.000187872597 * 0.000069396621 +
        4 * 0.797885 * 0.000119544623 * 0.000069396621 := by gcongr
    _ ≤ (1.52427E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13000 BstLean.Part154.csC Θ ≤ 0.002566528639 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13000 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13000 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13000 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035390013080 * 1.52427E-7 / (0.000245968646 : ℝ) := by gcongr
    _ ≤ 0.002566528639 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13000 BstLean.Part154.csC Θ ≤ 0.002846551691 + 0.000648521830 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13000 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13000 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035390013080 : ℝ) * ((2 * Θ * 0.000245969027 +
        (6863 / 10000) * 0.000245969027 * 13000 * 0.000983936609) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002846551691 + 0.000648521830 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13000 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13000 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13000 0.011 Θ ∧ gammaRatio 13000 0.011 Θ ≤ 0.000084557791 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13000 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035390013080 : ℝ) * 0.525 / ((1 - 0.011) * 13000) := by gcongr
      _ ≤ (0.000084557791 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13000 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13000 0.011 Θ) :=
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
    badAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13000 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13000 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13000 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13000 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13000 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13000 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13000 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13000 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13000 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13000 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035390013080 : ℝ) * 13000 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003229261452 + 0.003215050469 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13000

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13000
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13000 BstLean.Part154.csC) (piBar (rhoBar 13000 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13000 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13000 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13000 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13000 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13000 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13000 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13000 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13000 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13000 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13000 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051868661545 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13000) ≤ 0.010474156475 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13000 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035390013080)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010474156475 + 2 * 0.737676 / 13000) := by gcongr
    _ ≤ (0.051868661545 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13000 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13000

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13000
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516822100 : ℝ) ≤ plow 13000 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13000) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423762949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347427536) : eMP 13000 0.011 xi bn ≤ 0.001160402562 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13000 : ℝ) * (1 - 0.011))) ≤ 0.000573796438 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347427536 / (13000 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573796438 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573796438 : ℝ) + 3.141593 * 0.052423762949 / (13000 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160402562 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423762949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347427536) : PiBarMP 13000 12 0.011 xi bn ≤ 0.159360829878 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13000 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036707322649 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.388711960229 : ℝ) ≤ √((13000 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.017542509913 : ℝ) ≤ √(13000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13000) ≤ 0.122195303952 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036707322649 + 0.052423762949 * 1.772454 / (2 * (113.388711960229 : ℝ))) * (1 + 0.001160402562) +
        8 / (13000 * 114.017542509913) + 0.122195303952 := by gcongr
    _ ≤ (0.159360829878 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423762949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347427536) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280831022970) :
    parallelOracle 13000 0.011 xi bn cd ≤ 0.160327986388 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13000 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13000 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516822100 : ℝ) ≤ plow 13000 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.017542509913 : ℝ) ≤ √(13000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280831022970 : ℝ) / (2 * 0.560516822100 * 114.017542509913)) * 0.159360829878 +
        0.280831022970 ^ 2 / (2 * 0.560516822100 * 114.017542509913) := by gcongr
    _ ≤ (0.160327986388 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423762949) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347427536)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280831022970) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13000 13000 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516822100 : ℝ) ≤ plow 13000 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.017542509913 : ℝ) ≤ √(13000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13000 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13000 Θ 1.22 ≤ 0.011630670780 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.017542509913 := by gcongr <;> linarith
      _ ≤ (0.011630670780 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13000 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13000 13000 0.011 ≤ 0.008383683101 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13000 13000 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13000 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13000 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13000 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13000 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160327986388 + 0.011630670780 + (0.008383683101 : ℝ) *
        (1 + 2 * (0.280831022970 + 0.011630670780) / (0.560516822100 * 114.017542509913))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13000]

end BstLean.Part269.N13000

/-! The original eight local profiles supply actual 13000 moment certificates. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13000 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052423762949 ∧
    0 ≤ bN 13000 BstLean.Part154.csC (groupTheta g) ∧ bN 13000 BstLean.Part154.csC (groupTheta g) ≤ 0.001347427536 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13000 13000 0.011
      (momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13000 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13000 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13000 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228962361425 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13000 0.011
      (momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13000 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13000
/-! The actual computed-centre upper energy formula at 13000. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13000

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13000)
open BstLean.Part268 (cell13000)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084660114845
  | 2 => 0.085588788168
  | 3 => 0.086513670522
  | 4 => 0.087435726253
  | 5 => 0.088356135135
  | 6 => 0.089276326016
  | 7 => 0.090198013961
  | 8 => 0.091123240962
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13000 13000 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13000 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13000

/-! Actual upper energy certificates on all 43 source endpoints at 13000. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13000)
open BstLean.Part268 (cell13000)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13000 (gMinus 13000) (1 - (cell13000 i).lower) ≤ 1 ∧
    energyUpper 13000 (gMinus 13000) (BstLean.Part211.gPlus 13000)
      (finiteEnergy 13000 13000 0.011) (1 - (cell13000 i).lower) ≤
      (cell13000 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨10,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨11,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨12,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨13,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨14,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨15,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨16,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨17,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨18,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨19,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨20,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨21,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨22,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨23,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨24,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨25,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨26,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨27,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨28,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨29,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨30,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨31,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨32,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨33,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨34,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨35,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨36,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨37,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨38,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨39,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨40,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨41,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨42,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨43,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨44,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨45,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨46,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨47,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨48,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨49,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨50,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨51,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13000) (by norm_num)
        (q := 1 - (cell13000 ⟨52,by decide⟩).lower)
        (by norm_num [cell13000]) (by norm_num [cell13000])
      exact ⟨E.1,E.2.trans (by norm_num [cell13000])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13000

/-! Source-cell containment and simple scalar guards at 13000. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13000)
open BstLean.Part268 (cell13000)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13000 ⟨10,by decide⟩).lower ∧ (cell13000 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13000 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13000 ⟨11,by decide⟩).lower ∧ (cell13000 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13000 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13000 ⟨12,by decide⟩).lower ∧ (cell13000 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13000 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13000 ⟨13,by decide⟩).lower ∧ (cell13000 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13000 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13000 ⟨14,by decide⟩).lower ∧ (cell13000 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13000 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13000 ⟨15,by decide⟩).lower ∧ (cell13000 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13000 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13000 ⟨16,by decide⟩).lower ∧ (cell13000 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13000 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13000 ⟨17,by decide⟩).lower ∧ (cell13000 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13000 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13000 ⟨18,by decide⟩).lower ∧ (cell13000 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13000 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13000 ⟨19,by decide⟩).lower ∧ (cell13000 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13000 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13000 ⟨20,by decide⟩).lower ∧ (cell13000 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13000 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13000 ⟨21,by decide⟩).lower ∧ (cell13000 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13000 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13000 ⟨22,by decide⟩).lower ∧ (cell13000 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13000 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13000 ⟨23,by decide⟩).lower ∧ (cell13000 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13000 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13000 ⟨24,by decide⟩).lower ∧ (cell13000 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13000 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13000 ⟨25,by decide⟩).lower ∧ (cell13000 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13000 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13000 ⟨26,by decide⟩).lower ∧ (cell13000 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13000 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13000 ⟨27,by decide⟩).lower ∧ (cell13000 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13000 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13000 ⟨28,by decide⟩).lower ∧ (cell13000 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13000 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13000 ⟨29,by decide⟩).lower ∧ (cell13000 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13000 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13000 ⟨30,by decide⟩).lower ∧ (cell13000 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13000 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13000 ⟨31,by decide⟩).lower ∧ (cell13000 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13000 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13000 ⟨32,by decide⟩).lower ∧ (cell13000 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13000 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13000 ⟨33,by decide⟩).lower ∧ (cell13000 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13000 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13000 ⟨34,by decide⟩).lower ∧ (cell13000 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13000 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13000 ⟨35,by decide⟩).lower ∧ (cell13000 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13000 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13000 ⟨36,by decide⟩).lower ∧ (cell13000 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13000 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13000 ⟨37,by decide⟩).lower ∧ (cell13000 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13000 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13000 ⟨38,by decide⟩).lower ∧ (cell13000 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13000 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13000 ⟨39,by decide⟩).lower ∧ (cell13000 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13000 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13000 ⟨40,by decide⟩).lower ∧ (cell13000 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13000 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13000 ⟨41,by decide⟩).lower ∧ (cell13000 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13000 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13000 ⟨42,by decide⟩).lower ∧ (cell13000 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13000 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13000 ⟨43,by decide⟩).lower ∧ (cell13000 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13000 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13000 ⟨44,by decide⟩).lower ∧ (cell13000 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13000 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13000 ⟨45,by decide⟩).lower ∧ (cell13000 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13000 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13000 ⟨46,by decide⟩).lower ∧ (cell13000 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13000 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13000 ⟨47,by decide⟩).lower ∧ (cell13000 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13000 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13000 ⟨48,by decide⟩).lower ∧ (cell13000 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13000 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13000 ⟨49,by decide⟩).lower ∧ (cell13000 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13000 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13000 ⟨50,by decide⟩).lower ∧ (cell13000 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13000 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13000 ⟨51,by decide⟩).lower ∧ (cell13000 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13000 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13000 ⟨52,by decide⟩).lower ∧ (cell13000 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13000 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13000 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13000 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13000,cell13000,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13000 i).lower ∧
    (cell13000 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13000 i).upper ≤ (0.532 : ℝ) ∧
    (cell13000 i).centre ≤ (0.1 : ℝ) ∧ (cell13000 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13000 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13000 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13000

/-! The local source numeric instances at 13000 have no network premises. -/
namespace BstLean.Part269.N13000
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13000)
open BstLean.Part268 (cell13000)

noncomputable def sourceNumerics13000 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13000 (cell13000 i)
      scalarRow13000.M scalarRow13000.H scalarRow13000.xi := by
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
    energy_allowance := scalarRow13000.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13000]
    centre_nonneg := (scalarRow13000.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13000])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13000
/-! Actual 13001 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13001 ≤ (1.035388640171 : ℝ) := by
  have hr : (114.021927715681 : ℝ) ≤ √(13001 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.021927715681 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13001 13001 (11 / 1000) ≤
    (0.008383360667 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13001) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.021927715681 : ℝ) ≤ √(13001 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13001)
  have hdiv : K / √(13001 : ℝ) ≤ K / 114.021927715681 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.021927715681 ≤ (0.008383360667 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13001.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13001 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13001 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13001 := gPlus_lower 13001
end BstLean.Part269.N13001

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13001
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035388640170 : ℝ) ≤ wn 13001 := by
  have hn : √(13001 : ℝ) ≤ 114.021927715682 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13001 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.021927715682 ≤ 2 / √(13001 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245949401 : ℝ) ≤ rhoBar 13001 BstLean.Part154.csC ∧
    rhoBar 13001 BstLean.Part154.csC ≤ 0.000245949781 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035388640170 : ℝ) / (1.295212 * 13001) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035388640171 : ℝ) / (1.29521 * 13001) := by gcongr
      _ ≤ (0.000245949781 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13001 BstLean.Part154.csC) ≤ 0.000983859616 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13001 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) ≤ 0.000187857896 ∧
    cc1 (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) ≤ 0.000119535269 ∧
    cc2 (rhoBar 13001 BstLean.Part154.csC) ≤ 0.000069391191 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13001 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13001 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13001 BstLean.Part154.csC * nuR (rhoBar 13001 BstLean.Part154.csC)) ≤ 0.000491914685 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245949781 : ℝ) * 0.000983859616 := by gcongr
      _ ≤ (0.000491914685 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13001 BstLean.Part154.csC) * nuR (rhoBar 13001 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983859616 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13001 BstLean.Part154.csC) * rhoBar 13001 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245949781 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245949781 / 2 + 0.399 * 0.000983859616 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187857896 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491914685 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119535269 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245949781 / 1.414213562 := by gcongr
      _ ≤ (0.000069391191 : ℝ) := by norm_num

end BstLean.Part269.N13001

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13001
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) ≤ 1.52403E-7 := by
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13001 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13001 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13001 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187857896 : ℝ) ^ 2 + 0.000119535269 ^ 2 + 3 * 0.000069391191 ^ 2 +
        2 * 0.797885 * 0.000187857896 * 0.000119535269 + 2 * 0.000187857896 * 0.000069391191 +
        4 * 0.797885 * 0.000119535269 * 0.000069391191 := by gcongr
    _ ≤ (1.52403E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13001 BstLean.Part154.csC Θ ≤ 0.002566321923 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13001 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13001 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13001 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035388640171 * 1.52403E-7 / (0.000245949401 : ℝ) := by gcongr
    _ ≤ 0.002566321923 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13001 BstLean.Part154.csC Θ ≤ 0.002846321392 + 0.000648470227 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13001 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13001 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035388640171 : ℝ) * ((2 * Θ * 0.000245949781 +
        (6863 / 10000) * 0.000245949781 * 13001 * 0.000983859616) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002846321392 + 0.000648470227 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13001 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13001 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13001 0.011 Θ ∧ gammaRatio 13001 0.011 Θ ≤ 0.000084551175 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13001 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035388640171 : ℝ) * 0.525 / ((1 - 0.011) * 13001) := by gcongr
      _ ≤ (0.000084551175 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13001 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13001 0.011 Θ) :=
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
    badAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13001 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13001 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13001 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13001 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13001 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13001 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13001 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13001 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13001 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13001 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035388640171 : ℝ) * 13001 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003229031153 + 0.003214792150 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13001

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13001
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13001 BstLean.Part154.csC) (piBar (rhoBar 13001 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13001 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13001 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13001 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13001 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13001 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13001 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13001 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13001 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13001 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13001 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051866645330 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13001) ≤ 0.010473753646 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13001 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035388640171)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010473753646 + 2 * 0.737676 / 13001) := by gcongr
    _ ≤ (0.051866645330 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13001 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13001

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13001
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516865256 : ℝ) ≤ plow 13001 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13001) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423397032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347319010) : eMP 13001 0.011 xi bn ≤ 0.001160311137 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13001 : ℝ) * (1 - 0.011))) ≤ 0.000573751263 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347319010 / (13001 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573751263 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573751263 : ℝ) + 3.141593 * 0.052423397032 / (13001 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160311137 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423397032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347319010) : PiBarMP 13001 12 0.011 xi bn ≤ 0.159354627667 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13001 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036705844358 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.393072980671 : ℝ) ≤ √((13001 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.021927715681 : ℝ) ≤ √(13001 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13001) ≤ 0.122190604403 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036705844358 + 0.052423397032 * 1.772454 / (2 * (113.393072980671 : ℝ))) * (1 + 0.001160311137) +
        8 / (13001 * 114.021927715681) + 0.122190604403 := by gcongr
    _ ≤ (0.159354627667 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423397032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347319010) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280828207677) :
    parallelOracle 13001 0.011 xi bn cd ≤ 0.160321717400 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13001 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13001 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516865256 : ℝ) ≤ plow 13001 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.021927715681 : ℝ) ≤ √(13001 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280828207677 : ℝ) / (2 * 0.560516865256 * 114.021927715681)) * 0.159354627667 +
        0.280828207677 ^ 2 / (2 * 0.560516865256 * 114.021927715681) := by gcongr
    _ ≤ (0.160321717400 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423397032) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347319010)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280828207677) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13001 13001 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516865256 : ℝ) ≤ plow 13001 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.021927715681 : ℝ) ≤ √(13001 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13001 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13001 Θ 1.22 ≤ 0.011630223472 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.021927715681 := by gcongr <;> linarith
      _ ≤ (0.011630223472 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13001 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13001 13001 0.011 ≤ 0.008383360667 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13001 13001 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13001 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13001 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13001 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13001 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160321717400 + 0.011630223472 + (0.008383360667 : ℝ) *
        (1 + 2 * (0.280828207677 + 0.011630223472) / (0.560516865256 * 114.021927715681))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13001]

end BstLean.Part269.N13001

/-! The original eight local profiles supply actual 13001 moment certificates. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13001 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052423397032 ∧
    0 ≤ bN 13001 BstLean.Part154.csC (groupTheta g) ∧ bN 13001 BstLean.Part154.csC (groupTheta g) ≤ 0.001347319010 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13001 13001 0.011
      (momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13001 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13001 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13001 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228961562347 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13001 0.011
      (momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13001 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13001
/-! The actual computed-centre upper energy formula at 13001. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13001

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13001)
open BstLean.Part268 (cell13001)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084657496634
  | 2 => 0.085586135410
  | 3 => 0.086510977959
  | 4 => 0.087432987400
  | 5 => 0.088353342050
  | 6 => 0.089273469049
  | 7 => 0.090195081467
  | 8 => 0.091120218985
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13001 13001 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13001 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13001

/-! Actual upper energy certificates on all 43 source endpoints at 13001. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13001)
open BstLean.Part268 (cell13001)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13001 (gMinus 13001) (1 - (cell13001 i).lower) ≤ 1 ∧
    energyUpper 13001 (gMinus 13001) (BstLean.Part211.gPlus 13001)
      (finiteEnergy 13001 13001 0.011) (1 - (cell13001 i).lower) ≤
      (cell13001 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨10,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨11,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨12,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨13,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨14,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨15,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨16,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨17,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨18,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨19,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨20,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨21,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨22,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨23,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨24,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨25,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨26,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨27,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨28,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨29,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨30,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨31,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨32,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨33,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨34,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨35,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨36,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨37,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨38,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨39,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨40,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨41,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨42,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨43,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨44,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨45,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨46,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨47,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨48,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨49,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨50,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨51,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13001) (by norm_num)
        (q := 1 - (cell13001 ⟨52,by decide⟩).lower)
        (by norm_num [cell13001]) (by norm_num [cell13001])
      exact ⟨E.1,E.2.trans (by norm_num [cell13001])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13001

/-! Source-cell containment and simple scalar guards at 13001. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13001)
open BstLean.Part268 (cell13001)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13001 ⟨10,by decide⟩).lower ∧ (cell13001 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13001 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13001 ⟨11,by decide⟩).lower ∧ (cell13001 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13001 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13001 ⟨12,by decide⟩).lower ∧ (cell13001 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13001 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13001 ⟨13,by decide⟩).lower ∧ (cell13001 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13001 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13001 ⟨14,by decide⟩).lower ∧ (cell13001 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13001 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13001 ⟨15,by decide⟩).lower ∧ (cell13001 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13001 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13001 ⟨16,by decide⟩).lower ∧ (cell13001 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13001 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13001 ⟨17,by decide⟩).lower ∧ (cell13001 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13001 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13001 ⟨18,by decide⟩).lower ∧ (cell13001 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13001 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13001 ⟨19,by decide⟩).lower ∧ (cell13001 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13001 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13001 ⟨20,by decide⟩).lower ∧ (cell13001 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13001 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13001 ⟨21,by decide⟩).lower ∧ (cell13001 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13001 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13001 ⟨22,by decide⟩).lower ∧ (cell13001 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13001 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13001 ⟨23,by decide⟩).lower ∧ (cell13001 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13001 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13001 ⟨24,by decide⟩).lower ∧ (cell13001 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13001 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13001 ⟨25,by decide⟩).lower ∧ (cell13001 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13001 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13001 ⟨26,by decide⟩).lower ∧ (cell13001 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13001 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13001 ⟨27,by decide⟩).lower ∧ (cell13001 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13001 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13001 ⟨28,by decide⟩).lower ∧ (cell13001 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13001 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13001 ⟨29,by decide⟩).lower ∧ (cell13001 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13001 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13001 ⟨30,by decide⟩).lower ∧ (cell13001 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13001 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13001 ⟨31,by decide⟩).lower ∧ (cell13001 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13001 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13001 ⟨32,by decide⟩).lower ∧ (cell13001 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13001 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13001 ⟨33,by decide⟩).lower ∧ (cell13001 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13001 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13001 ⟨34,by decide⟩).lower ∧ (cell13001 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13001 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13001 ⟨35,by decide⟩).lower ∧ (cell13001 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13001 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13001 ⟨36,by decide⟩).lower ∧ (cell13001 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13001 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13001 ⟨37,by decide⟩).lower ∧ (cell13001 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13001 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13001 ⟨38,by decide⟩).lower ∧ (cell13001 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13001 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13001 ⟨39,by decide⟩).lower ∧ (cell13001 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13001 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13001 ⟨40,by decide⟩).lower ∧ (cell13001 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13001 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13001 ⟨41,by decide⟩).lower ∧ (cell13001 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13001 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13001 ⟨42,by decide⟩).lower ∧ (cell13001 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13001 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13001 ⟨43,by decide⟩).lower ∧ (cell13001 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13001 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13001 ⟨44,by decide⟩).lower ∧ (cell13001 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13001 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13001 ⟨45,by decide⟩).lower ∧ (cell13001 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13001 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13001 ⟨46,by decide⟩).lower ∧ (cell13001 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13001 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13001 ⟨47,by decide⟩).lower ∧ (cell13001 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13001 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13001 ⟨48,by decide⟩).lower ∧ (cell13001 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13001 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13001 ⟨49,by decide⟩).lower ∧ (cell13001 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13001 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13001 ⟨50,by decide⟩).lower ∧ (cell13001 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13001 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13001 ⟨51,by decide⟩).lower ∧ (cell13001 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13001 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13001 ⟨52,by decide⟩).lower ∧ (cell13001 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13001 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13001 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13001 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13001,cell13001,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13001 i).lower ∧
    (cell13001 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13001 i).upper ≤ (0.532 : ℝ) ∧
    (cell13001 i).centre ≤ (0.1 : ℝ) ∧ (cell13001 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13001 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13001 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13001

/-! The local source numeric instances at 13001 have no network premises. -/
namespace BstLean.Part269.N13001
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13001)
open BstLean.Part268 (cell13001)

noncomputable def sourceNumerics13001 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13001 (cell13001 i)
      scalarRow13001.M scalarRow13001.H scalarRow13001.xi := by
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
    energy_allowance := scalarRow13001.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13001]
    centre_nonneg := (scalarRow13001.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13001])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13001
/-! Actual 13002 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13002 ≤ (1.035387267422 : ℝ) := by
  have hr : (114.026312752802 : ℝ) ≤ √(13002 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.026312752802 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13002 13002 (11 / 1000) ≤
    (0.008383038271 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13002) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.026312752802 : ℝ) ≤ √(13002 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13002)
  have hdiv : K / √(13002 : ℝ) ≤ K / 114.026312752802 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.026312752802 ≤ (0.008383038271 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13002.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13002 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13002 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13002 := gPlus_lower 13002
end BstLean.Part269.N13002

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13002
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035387267421 : ℝ) ≤ wn 13002 := by
  have hn : √(13002 : ℝ) ≤ 114.026312752803 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13002 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.026312752803 ≤ 2 / √(13002 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245930158 : ℝ) ≤ rhoBar 13002 BstLean.Part154.csC ∧
    rhoBar 13002 BstLean.Part154.csC ≤ 0.000245930539 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035387267421 : ℝ) / (1.295212 * 13002) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035387267422 : ℝ) / (1.29521 * 13002) := by gcongr
      _ ≤ (0.000245930539 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13002 BstLean.Part154.csC) ≤ 0.000983782638 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13002 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) ≤ 0.000187843198 ∧
    cc1 (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) ≤ 0.000119525917 ∧
    cc2 (rhoBar 13002 BstLean.Part154.csC) ≤ 0.000069385762 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13002 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13002 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13002 BstLean.Part154.csC * nuR (rhoBar 13002 BstLean.Part154.csC)) ≤ 0.000491876199 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245930539 : ℝ) * 0.000983782638 := by gcongr
      _ ≤ (0.000491876199 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13002 BstLean.Part154.csC) * nuR (rhoBar 13002 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983782638 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13002 BstLean.Part154.csC) * rhoBar 13002 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245930539 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245930539 / 2 + 0.399 * 0.000983782638 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187843198 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491876199 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119525917 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245930539 / 1.414213562 := by gcongr
      _ ≤ (0.000069385762 : ℝ) := by norm_num

end BstLean.Part269.N13002

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13002
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) ≤ 1.52380E-7 := by
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13002 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13002 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13002 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187843198 : ℝ) ^ 2 + 0.000119525917 ^ 2 + 3 * 0.000069385762 ^ 2 +
        2 * 0.797885 * 0.000187843198 * 0.000119525917 + 2 * 0.000187843198 * 0.000069385762 +
        4 * 0.797885 * 0.000119525917 * 0.000069385762 := by gcongr
    _ ≤ (1.52380E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13002 BstLean.Part154.csC Θ ≤ 0.002566131997 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13002 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13002 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13002 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035387267422 * 1.52380E-7 / (0.000245930158 : ℝ) := by gcongr
    _ ≤ 0.002566131997 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13002 BstLean.Part154.csC Θ ≤ 0.002846091151 + 0.000648418633 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13002 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13002 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035387267422 : ℝ) * ((2 * Θ * 0.000245930539 +
        (6863 / 10000) * 0.000245930539 * 13002 * 0.000983782638) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002846091151 + 0.000648418633 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13002 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13002 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13002 0.011 Θ ∧ gammaRatio 13002 0.011 Θ ≤ 0.000084544560 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13002 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035387267422 : ℝ) * 0.525 / ((1 - 0.011) * 13002) := by gcongr
      _ ≤ (0.000084544560 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13002 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13002 0.011 Θ) :=
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
    badAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13002 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13002 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13002 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13002 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13002 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13002 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13002 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13002 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13002 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13002 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035387267422 : ℝ) * 13002 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003228800912 + 0.003214550630 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13002

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13002
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13002 BstLean.Part154.csC) (piBar (rhoBar 13002 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13002 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13002 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13002 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13002 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13002 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13002 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13002 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13002 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13002 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13002 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051864629346 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13002) ≤ 0.010473350863 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13002 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035387267422)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010473350863 + 2 * 0.737676 / 13002) := by gcongr
    _ ≤ (0.051864629346 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13002 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13002

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13002
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516908406 : ℝ) ≤ plow 13002 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13002) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423039993)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347219299) : eMP 13002 0.011 xi bn ≤ 0.001160223475 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13002 : ℝ) * (1 - 0.011))) ≤ 0.000573707968 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347219299 / (13002 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573707968 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573707968 : ℝ) + 3.141593 * 0.052423039993 / (13002 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160223475 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423039993)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347219299) : PiBarMP 13002 12 0.011 xi bn ≤ 0.159348546372 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13002 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036704486089 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.397433833398 : ℝ) ≤ √((13002 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.026312752802 : ℝ) ≤ √(13002 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13002) ≤ 0.122185905397 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036704486089 + 0.052423039993 * 1.772454 / (2 * (113.397433833398 : ℝ))) * (1 + 0.001160223475) +
        8 / (13002 * 114.026312752802) + 0.122185905397 := by gcongr
    _ ≤ (0.159348546372 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423039993)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347219299) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280825411999) :
    parallelOracle 13002 0.011 xi bn cd ≤ 0.160315569711 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13002 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13002 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516908406 : ℝ) ≤ plow 13002 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.026312752802 : ℝ) ≤ √(13002 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280825411999 : ℝ) / (2 * 0.560516908406 * 114.026312752802)) * 0.159348546372 +
        0.280825411999 ^ 2 / (2 * 0.560516908406 * 114.026312752802) := by gcongr
    _ ≤ (0.160315569711 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052423039993) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347219299)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280825411999) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13002 13002 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516908406 : ℝ) ≤ plow 13002 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.026312752802 : ℝ) ≤ √(13002 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13002 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13002 Θ 1.22 ≤ 0.011629776216 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.026312752802 := by gcongr <;> linarith
      _ ≤ (0.011629776216 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13002 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13002 13002 0.011 ≤ 0.008383038271 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13002 13002 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13002 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13002 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13002 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13002 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160315569711 + 0.011629776216 + (0.008383038271 : ℝ) *
        (1 + 2 * (0.280825411999 + 0.011629776216) / (0.560516908406 * 114.026312752802))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13002]

end BstLean.Part269.N13002

/-! The original eight local profiles supply actual 13002 moment certificates. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13002 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052423039993 ∧
    0 ≤ bN 13002 BstLean.Part154.csC (groupTheta g) ∧ bN 13002 BstLean.Part154.csC (groupTheta g) ≤ 0.001347219299 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13002 13002 0.011
      (momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13002 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13002 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13002 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228960782653 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13002 0.011
      (momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13002 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13002
/-! The actual computed-centre upper energy formula at 13002. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13002

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13002)
open BstLean.Part268 (cell13002)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084654879230
  | 2 => 0.085583483486
  | 3 => 0.086508286268
  | 4 => 0.087430249462
  | 5 => 0.088350549933
  | 6 => 0.089270613115
  | 7 => 0.090192150086
  | 8 => 0.091117198217
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13002 13002 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13002 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13002

/-! Actual upper energy certificates on all 43 source endpoints at 13002. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13002)
open BstLean.Part268 (cell13002)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13002 (gMinus 13002) (1 - (cell13002 i).lower) ≤ 1 ∧
    energyUpper 13002 (gMinus 13002) (BstLean.Part211.gPlus 13002)
      (finiteEnergy 13002 13002 0.011) (1 - (cell13002 i).lower) ≤
      (cell13002 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨10,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨11,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨12,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨13,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨14,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨15,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨16,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨17,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨18,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨19,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨20,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨21,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨22,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨23,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨24,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨25,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨26,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨27,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨28,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨29,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨30,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨31,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨32,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨33,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨34,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨35,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨36,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨37,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨38,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨39,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨40,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨41,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨42,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨43,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨44,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨45,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨46,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨47,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨48,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨49,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨50,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨51,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13002) (by norm_num)
        (q := 1 - (cell13002 ⟨52,by decide⟩).lower)
        (by norm_num [cell13002]) (by norm_num [cell13002])
      exact ⟨E.1,E.2.trans (by norm_num [cell13002])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13002

/-! Source-cell containment and simple scalar guards at 13002. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13002)
open BstLean.Part268 (cell13002)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13002 ⟨10,by decide⟩).lower ∧ (cell13002 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13002 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13002 ⟨11,by decide⟩).lower ∧ (cell13002 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13002 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13002 ⟨12,by decide⟩).lower ∧ (cell13002 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13002 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13002 ⟨13,by decide⟩).lower ∧ (cell13002 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13002 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13002 ⟨14,by decide⟩).lower ∧ (cell13002 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13002 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13002 ⟨15,by decide⟩).lower ∧ (cell13002 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13002 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13002 ⟨16,by decide⟩).lower ∧ (cell13002 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13002 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13002 ⟨17,by decide⟩).lower ∧ (cell13002 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13002 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13002 ⟨18,by decide⟩).lower ∧ (cell13002 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13002 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13002 ⟨19,by decide⟩).lower ∧ (cell13002 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13002 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13002 ⟨20,by decide⟩).lower ∧ (cell13002 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13002 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13002 ⟨21,by decide⟩).lower ∧ (cell13002 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13002 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13002 ⟨22,by decide⟩).lower ∧ (cell13002 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13002 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13002 ⟨23,by decide⟩).lower ∧ (cell13002 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13002 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13002 ⟨24,by decide⟩).lower ∧ (cell13002 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13002 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13002 ⟨25,by decide⟩).lower ∧ (cell13002 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13002 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13002 ⟨26,by decide⟩).lower ∧ (cell13002 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13002 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13002 ⟨27,by decide⟩).lower ∧ (cell13002 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13002 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13002 ⟨28,by decide⟩).lower ∧ (cell13002 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13002 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13002 ⟨29,by decide⟩).lower ∧ (cell13002 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13002 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13002 ⟨30,by decide⟩).lower ∧ (cell13002 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13002 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13002 ⟨31,by decide⟩).lower ∧ (cell13002 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13002 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13002 ⟨32,by decide⟩).lower ∧ (cell13002 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13002 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13002 ⟨33,by decide⟩).lower ∧ (cell13002 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13002 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13002 ⟨34,by decide⟩).lower ∧ (cell13002 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13002 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13002 ⟨35,by decide⟩).lower ∧ (cell13002 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13002 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13002 ⟨36,by decide⟩).lower ∧ (cell13002 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13002 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13002 ⟨37,by decide⟩).lower ∧ (cell13002 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13002 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13002 ⟨38,by decide⟩).lower ∧ (cell13002 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13002 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13002 ⟨39,by decide⟩).lower ∧ (cell13002 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13002 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13002 ⟨40,by decide⟩).lower ∧ (cell13002 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13002 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13002 ⟨41,by decide⟩).lower ∧ (cell13002 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13002 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13002 ⟨42,by decide⟩).lower ∧ (cell13002 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13002 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13002 ⟨43,by decide⟩).lower ∧ (cell13002 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13002 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13002 ⟨44,by decide⟩).lower ∧ (cell13002 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13002 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13002 ⟨45,by decide⟩).lower ∧ (cell13002 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13002 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13002 ⟨46,by decide⟩).lower ∧ (cell13002 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13002 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13002 ⟨47,by decide⟩).lower ∧ (cell13002 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13002 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13002 ⟨48,by decide⟩).lower ∧ (cell13002 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13002 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13002 ⟨49,by decide⟩).lower ∧ (cell13002 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13002 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13002 ⟨50,by decide⟩).lower ∧ (cell13002 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13002 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13002 ⟨51,by decide⟩).lower ∧ (cell13002 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13002 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13002 ⟨52,by decide⟩).lower ∧ (cell13002 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13002 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13002 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13002 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13002,cell13002,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13002 i).lower ∧
    (cell13002 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13002 i).upper ≤ (0.532 : ℝ) ∧
    (cell13002 i).centre ≤ (0.1 : ℝ) ∧ (cell13002 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13002 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13002 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13002

/-! The local source numeric instances at 13002 have no network premises. -/
namespace BstLean.Part269.N13002
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13002)
open BstLean.Part268 (cell13002)

noncomputable def sourceNumerics13002 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13002 (cell13002 i)
      scalarRow13002.M scalarRow13002.H scalarRow13002.xi := by
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
    energy_allowance := scalarRow13002.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13002]
    centre_nonneg := (scalarRow13002.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13002])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13002
/-! Actual 13003 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13003 ≤ (1.035385894831 : ℝ) := by
  have hr : (114.030697621298 : ℝ) ≤ √(13003 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.030697621298 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13003 13003 (11 / 1000) ≤
    (0.008382715913 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13003) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.030697621298 : ℝ) ≤ √(13003 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13003)
  have hdiv : K / √(13003 : ℝ) ≤ K / 114.030697621298 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.030697621298 ≤ (0.008382715913 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13003.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13003 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13003 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13003 := gPlus_lower 13003
end BstLean.Part269.N13003

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13003
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035385894830 : ℝ) ≤ wn 13003 := by
  have hn : √(13003 : ℝ) ≤ 114.030697621299 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13003 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.030697621299 ≤ 2 / √(13003 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245910919 : ℝ) ≤ rhoBar 13003 BstLean.Part154.csC ∧
    rhoBar 13003 BstLean.Part154.csC ≤ 0.000245911300 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035385894830 : ℝ) / (1.295212 * 13003) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035385894831 : ℝ) / (1.29521 * 13003) := by gcongr
      _ ≤ (0.000245911300 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13003 BstLean.Part154.csC) ≤ 0.000983705673 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13003 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) ≤ 0.000187828503 ∧
    cc1 (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) ≤ 0.000119516566 ∧
    cc2 (rhoBar 13003 BstLean.Part154.csC) ≤ 0.000069380334 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13003 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13003 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13003 BstLean.Part154.csC * nuR (rhoBar 13003 BstLean.Part154.csC)) ≤ 0.000491837719 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245911300 : ℝ) * 0.000983705673 := by gcongr
      _ ≤ (0.000491837719 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13003 BstLean.Part154.csC) * nuR (rhoBar 13003 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983705673 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13003 BstLean.Part154.csC) * rhoBar 13003 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245911300 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245911300 / 2 + 0.399 * 0.000983705673 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187828503 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491837719 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119516566 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245911300 / 1.414213562 := by gcongr
      _ ≤ (0.000069380334 : ℝ) := by norm_num

end BstLean.Part269.N13003

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13003
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) ≤ 1.52356E-7 := by
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13003 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13003 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13003 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187828503 : ℝ) ^ 2 + 0.000119516566 ^ 2 + 3 * 0.000069380334 ^ 2 +
        2 * 0.797885 * 0.000187828503 * 0.000119516566 + 2 * 0.000187828503 * 0.000069380334 +
        4 * 0.797885 * 0.000119516566 * 0.000069380334 := by gcongr
    _ ≤ (1.52356E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13003 BstLean.Part154.csC Θ ≤ 0.002565925158 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13003 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13003 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13003 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035385894831 * 1.52356E-7 / (0.000245910919 : ℝ) := by gcongr
    _ ≤ 0.002565925158 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13003 BstLean.Part154.csC Θ ≤ 0.002845860950 + 0.000648367049 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13003 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13003 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035385894831 : ℝ) * ((2 * Θ * 0.000245911300 +
        (6863 / 10000) * 0.000245911300 * 13003 * 0.000983705673) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002845860950 + 0.000648367049 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13003 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13003 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13003 0.011 Θ ∧ gammaRatio 13003 0.011 Θ ≤ 0.000084537946 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13003 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035385894831 : ℝ) * 0.525 / ((1 - 0.011) * 13003) := by gcongr
      _ ≤ (0.000084537946 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13003 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13003 0.011 Θ) :=
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
    badAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13003 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13003 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13003 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13003 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13003 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13003 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13003 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13003 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13003 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13003 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035385894831 : ℝ) * 13003 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003228570711 + 0.003214292207 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13003

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13003
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13003 BstLean.Part154.csC) (piBar (rhoBar 13003 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13003 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13003 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13003 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13003 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13003 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13003 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13003 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13003 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13003 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13003 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051862613600 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13003) ≤ 0.010472948127 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13003 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035385894831)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010472948127 + 2 * 0.737676 / 13003) := by gcongr
    _ ≤ (0.051862613600 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13003 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13003

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13003
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516951549 : ℝ) ≤ plow 13003 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13003) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422674120)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347110708) : eMP 13003 0.011 xi bn ≤ 0.001160132037 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13003 : ℝ) * (1 - 0.011))) ≤ 0.000573662786 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347110708 / (13003 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573662786 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573662786 : ℝ) + 3.141593 * 0.052422674120 / (13003 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160132037 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422674120)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347110708) : PiBarMP 13003 12 0.011 xi bn ≤ 0.159342344249 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13003 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036703006798 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.401794518429 : ℝ) ≤ √((13003 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.030697621298 : ℝ) ≤ √(13003 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13003) ≤ 0.122181206933 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036703006798 + 0.052422674120 * 1.772454 / (2 * (113.401794518429 : ℝ))) * (1 + 0.001160132037) +
        8 / (13003 * 114.030697621298) + 0.122181206933 := by gcongr
    _ ≤ (0.159342344249 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422674120)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347110708) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280822597266) :
    parallelOracle 13003 0.011 xi bn cd ≤ 0.160309300827 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13003 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13003 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516951549 : ℝ) ≤ plow 13003 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.030697621298 : ℝ) ≤ √(13003 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280822597266 : ℝ) / (2 * 0.560516951549 * 114.030697621298)) * 0.159342344249 +
        0.280822597266 ^ 2 / (2 * 0.560516951549 * 114.030697621298) := by gcongr
    _ ≤ (0.160309300827 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422674120) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347110708)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280822597266) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13003 13003 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516951549 : ℝ) ≤ plow 13003 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.030697621298 : ℝ) ≤ √(13003 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13003 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13003 Θ 1.22 ≤ 0.011629329012 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.030697621298 := by gcongr <;> linarith
      _ ≤ (0.011629329012 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13003 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13003 13003 0.011 ≤ 0.008382715913 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13003 13003 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13003 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13003 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13003 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13003 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160309300827 + 0.011629329012 + (0.008382715913 : ℝ) *
        (1 + 2 * (0.280822597266 + 0.011629329012) / (0.560516951549 * 114.030697621298))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13003]

end BstLean.Part269.N13003

/-! The original eight local profiles supply actual 13003 moment certificates. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13003 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052422674120 ∧
    0 ≤ bN 13003 BstLean.Part154.csC (groupTheta g) ∧ bN 13003 BstLean.Part154.csC (groupTheta g) ≤ 0.001347110708 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13003 13003 0.011
      (momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13003 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13003 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13003 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228959983666 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13003 0.011
      (momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13003 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13003
/-! The actual computed-centre upper energy formula at 13003. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13003

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13003)
open BstLean.Part268 (cell13003)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084652262631
  | 2 => 0.085580832398
  | 3 => 0.086505595446
  | 4 => 0.087427512437
  | 5 => 0.088347758783
  | 6 => 0.089267758213
  | 7 => 0.090189219817
  | 8 => 0.091114178656
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13003 13003 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13003 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13003

/-! Actual upper energy certificates on all 43 source endpoints at 13003. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13003)
open BstLean.Part268 (cell13003)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13003 (gMinus 13003) (1 - (cell13003 i).lower) ≤ 1 ∧
    energyUpper 13003 (gMinus 13003) (BstLean.Part211.gPlus 13003)
      (finiteEnergy 13003 13003 0.011) (1 - (cell13003 i).lower) ≤
      (cell13003 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨10,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨11,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨12,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨13,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨14,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨15,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨16,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨17,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨18,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨19,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨20,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨21,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨22,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨23,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨24,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨25,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨26,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨27,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨28,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨29,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨30,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨31,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨32,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨33,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨34,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨35,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨36,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨37,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨38,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨39,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨40,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨41,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨42,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨43,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨44,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨45,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨46,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨47,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨48,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨49,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨50,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨51,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13003) (by norm_num)
        (q := 1 - (cell13003 ⟨52,by decide⟩).lower)
        (by norm_num [cell13003]) (by norm_num [cell13003])
      exact ⟨E.1,E.2.trans (by norm_num [cell13003])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13003

/-! Source-cell containment and simple scalar guards at 13003. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13003)
open BstLean.Part268 (cell13003)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13003 ⟨10,by decide⟩).lower ∧ (cell13003 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13003 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13003 ⟨11,by decide⟩).lower ∧ (cell13003 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13003 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13003 ⟨12,by decide⟩).lower ∧ (cell13003 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13003 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13003 ⟨13,by decide⟩).lower ∧ (cell13003 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13003 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13003 ⟨14,by decide⟩).lower ∧ (cell13003 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13003 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13003 ⟨15,by decide⟩).lower ∧ (cell13003 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13003 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13003 ⟨16,by decide⟩).lower ∧ (cell13003 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13003 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13003 ⟨17,by decide⟩).lower ∧ (cell13003 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13003 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13003 ⟨18,by decide⟩).lower ∧ (cell13003 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13003 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13003 ⟨19,by decide⟩).lower ∧ (cell13003 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13003 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13003 ⟨20,by decide⟩).lower ∧ (cell13003 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13003 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13003 ⟨21,by decide⟩).lower ∧ (cell13003 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13003 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13003 ⟨22,by decide⟩).lower ∧ (cell13003 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13003 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13003 ⟨23,by decide⟩).lower ∧ (cell13003 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13003 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13003 ⟨24,by decide⟩).lower ∧ (cell13003 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13003 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13003 ⟨25,by decide⟩).lower ∧ (cell13003 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13003 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13003 ⟨26,by decide⟩).lower ∧ (cell13003 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13003 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13003 ⟨27,by decide⟩).lower ∧ (cell13003 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13003 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13003 ⟨28,by decide⟩).lower ∧ (cell13003 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13003 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13003 ⟨29,by decide⟩).lower ∧ (cell13003 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13003 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13003 ⟨30,by decide⟩).lower ∧ (cell13003 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13003 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13003 ⟨31,by decide⟩).lower ∧ (cell13003 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13003 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13003 ⟨32,by decide⟩).lower ∧ (cell13003 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13003 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13003 ⟨33,by decide⟩).lower ∧ (cell13003 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13003 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13003 ⟨34,by decide⟩).lower ∧ (cell13003 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13003 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13003 ⟨35,by decide⟩).lower ∧ (cell13003 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13003 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13003 ⟨36,by decide⟩).lower ∧ (cell13003 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13003 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13003 ⟨37,by decide⟩).lower ∧ (cell13003 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13003 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13003 ⟨38,by decide⟩).lower ∧ (cell13003 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13003 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13003 ⟨39,by decide⟩).lower ∧ (cell13003 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13003 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13003 ⟨40,by decide⟩).lower ∧ (cell13003 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13003 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13003 ⟨41,by decide⟩).lower ∧ (cell13003 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13003 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13003 ⟨42,by decide⟩).lower ∧ (cell13003 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13003 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13003 ⟨43,by decide⟩).lower ∧ (cell13003 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13003 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13003 ⟨44,by decide⟩).lower ∧ (cell13003 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13003 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13003 ⟨45,by decide⟩).lower ∧ (cell13003 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13003 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13003 ⟨46,by decide⟩).lower ∧ (cell13003 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13003 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13003 ⟨47,by decide⟩).lower ∧ (cell13003 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13003 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13003 ⟨48,by decide⟩).lower ∧ (cell13003 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13003 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13003 ⟨49,by decide⟩).lower ∧ (cell13003 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13003 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13003 ⟨50,by decide⟩).lower ∧ (cell13003 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13003 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13003 ⟨51,by decide⟩).lower ∧ (cell13003 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13003 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13003 ⟨52,by decide⟩).lower ∧ (cell13003 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13003 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13003 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13003 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13003,cell13003,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13003 i).lower ∧
    (cell13003 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13003 i).upper ≤ (0.532 : ℝ) ∧
    (cell13003 i).centre ≤ (0.1 : ℝ) ∧ (cell13003 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13003 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13003 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13003

/-! The local source numeric instances at 13003 have no network premises. -/
namespace BstLean.Part269.N13003
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13003)
open BstLean.Part268 (cell13003)

noncomputable def sourceNumerics13003 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13003 (cell13003 i)
      scalarRow13003.M scalarRow13003.H scalarRow13003.xi := by
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
    energy_allowance := scalarRow13003.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13003]
    centre_nonneg := (scalarRow13003.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13003])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13003
/-! Actual 13004 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13004 ≤ (1.035384522400 : ℝ) := by
  have hr : (114.035082321187 : ℝ) ≤ √(13004 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.035082321187 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13004 13004 (11 / 1000) ≤
    (0.008382393591 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13004) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.035082321187 : ℝ) ≤ √(13004 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13004)
  have hdiv : K / √(13004 : ℝ) ≤ K / 114.035082321187 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.035082321187 ≤ (0.008382393591 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13004.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13004 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13004 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13004 := gPlus_lower 13004
end BstLean.Part269.N13004

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13004
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035384522399 : ℝ) ≤ wn 13004 := by
  have hn : √(13004 : ℝ) ≤ 114.035082321188 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13004 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.035082321188 ≤ 2 / √(13004 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245891683 : ℝ) ≤ rhoBar 13004 BstLean.Part154.csC ∧
    rhoBar 13004 BstLean.Part154.csC ≤ 0.000245892063 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035384522399 : ℝ) / (1.295212 * 13004) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035384522400 : ℝ) / (1.29521 * 13004) := by gcongr
      _ ≤ (0.000245892063 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13004 BstLean.Part154.csC) ≤ 0.000983628715 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13004 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) ≤ 0.000187813809 ∧
    cc1 (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) ≤ 0.000119507216 ∧
    cc2 (rhoBar 13004 BstLean.Part154.csC) ≤ 0.000069374907 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13004 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13004 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13004 BstLean.Part154.csC * nuR (rhoBar 13004 BstLean.Part154.csC)) ≤ 0.000491799242 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245892063 : ℝ) * 0.000983628715 := by gcongr
      _ ≤ (0.000491799242 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13004 BstLean.Part154.csC) * nuR (rhoBar 13004 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983628715 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13004 BstLean.Part154.csC) * rhoBar 13004 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245892063 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245892063 / 2 + 0.399 * 0.000983628715 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187813809 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491799242 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119507216 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245892063 / 1.414213562 := by gcongr
      _ ≤ (0.000069374907 : ℝ) := by norm_num

end BstLean.Part269.N13004

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13004
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) ≤ 1.52332E-7 := by
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13004 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13004 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13004 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187813809 : ℝ) ^ 2 + 0.000119507216 ^ 2 + 3 * 0.000069374907 ^ 2 +
        2 * 0.797885 * 0.000187813809 * 0.000119507216 + 2 * 0.000187813809 * 0.000069374907 +
        4 * 0.797885 * 0.000119507216 * 0.000069374907 := by gcongr
    _ ≤ (1.52332E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13004 BstLean.Part154.csC Θ ≤ 0.002565718257 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13004 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13004 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13004 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035384522400 * 1.52332E-7 / (0.000245891683 : ℝ) := by gcongr
    _ ≤ 0.002565718257 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13004 BstLean.Part154.csC Θ ≤ 0.002845630759 + 0.000648315469 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13004 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13004 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035384522400 : ℝ) * ((2 * Θ * 0.000245892063 +
        (6863 / 10000) * 0.000245892063 * 13004 * 0.000983628715) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002845630759 + 0.000648315469 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13004 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13004 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13004 0.011 Θ ∧ gammaRatio 13004 0.011 Θ ≤ 0.000084531333 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13004 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035384522400 : ℝ) * 0.525 / ((1 - 0.011) * 13004) := by gcongr
      _ ≤ (0.000084531333 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13004 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13004 0.011 Θ) :=
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
    badAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13004 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13004 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13004 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13004 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13004 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13004 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13004 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13004 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13004 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13004 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035384522400 : ℝ) * 13004 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003228340520 + 0.003214033726 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13004

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13004
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13004 BstLean.Part154.csC) (piBar (rhoBar 13004 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13004 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13004 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13004 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13004 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13004 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13004 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13004 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13004 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13004 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13004 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051860598090 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13004) ≤ 0.010472545438 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13004 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035384522400)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010472545438 + 2 * 0.737676 / 13004) := by gcongr
    _ ≤ (0.051860598090 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13004 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13004

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13004
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560516994686 : ℝ) ≤ plow 13004 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13004) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422308227)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347002085) : eMP 13004 0.011 xi bn ≤ 0.001160040590 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13004 : ℝ) * (1 - 0.011))) ≤ 0.000573617600 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001347002085 / (13004 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573617600 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573617600 : ℝ) + 3.141593 * 0.052422308227 / (13004 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001160040590 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422308227)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347002085) : PiBarMP 13004 12 0.011 xi bn ≤ 0.159336142175 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13004 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036701527012 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.406155035782 : ℝ) ≤ √((13004 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.035082321187 : ℝ) ≤ √(13004 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13004) ≤ 0.122176509011 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036701527012 + 0.052422308227 * 1.772454 / (2 * (113.406155035782 : ℝ))) * (1 + 0.001160040590) +
        8 / (13004 * 114.035082321187) + 0.122176509011 := by gcongr
    _ ≤ (0.159336142175 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422308227)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347002085) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280819782722) :
    parallelOracle 13004 0.011 xi bn cd ≤ 0.160303032001 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13004 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13004 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560516994686 : ℝ) ≤ plow 13004 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.035082321187 : ℝ) ≤ √(13004 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280819782722 : ℝ) / (2 * 0.560516994686 * 114.035082321187)) * 0.159336142175 +
        0.280819782722 ^ 2 / (2 * 0.560516994686 * 114.035082321187) := by gcongr
    _ ≤ (0.160303032001 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052422308227) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001347002085)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280819782722) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13004 13004 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560516994686 : ℝ) ≤ plow 13004 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.035082321187 : ℝ) ≤ √(13004 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13004 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13004 Θ 1.22 ≤ 0.011628881859 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.035082321187 := by gcongr <;> linarith
      _ ≤ (0.011628881859 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13004 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13004 13004 0.011 ≤ 0.008382393591 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13004 13004 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13004 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13004 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13004 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13004 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160303032001 + 0.011628881859 + (0.008382393591 : ℝ) *
        (1 + 2 * (0.280819782722 + 0.011628881859) / (0.560516994686 * 114.035082321187))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13004]

end BstLean.Part269.N13004

/-! The original eight local profiles supply actual 13004 moment certificates. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13004 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052422308227 ∧
    0 ≤ bN 13004 BstLean.Part154.csC (groupTheta g) ∧ bN 13004 BstLean.Part154.csC (groupTheta g) ≤ 0.001347002085 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13004 13004 0.011
      (momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13004 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13004 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13004 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228959184632 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13004 0.011
      (momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13004 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13004
/-! The actual computed-centre upper energy formula at 13004. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13004

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13004)
open BstLean.Part268 (cell13004)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084649646839
  | 2 => 0.085578182143
  | 3 => 0.086502905493
  | 4 => 0.087424776324
  | 5 => 0.088344968599
  | 6 => 0.089264904343
  | 7 => 0.090186290658
  | 8 => 0.091111160302
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13004 13004 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13004 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13004

/-! Actual upper energy certificates on all 43 source endpoints at 13004. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13004)
open BstLean.Part268 (cell13004)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13004 (gMinus 13004) (1 - (cell13004 i).lower) ≤ 1 ∧
    energyUpper 13004 (gMinus 13004) (BstLean.Part211.gPlus 13004)
      (finiteEnergy 13004 13004 0.011) (1 - (cell13004 i).lower) ≤
      (cell13004 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨10,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨11,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨12,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨13,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨14,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨15,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨16,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨17,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨18,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨19,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨20,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨21,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨22,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨23,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨24,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨25,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨26,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨27,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨28,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨29,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨30,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨31,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨32,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨33,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨34,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨35,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨36,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨37,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨38,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨39,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨40,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨41,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨42,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨43,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨44,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨45,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨46,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨47,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨48,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨49,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨50,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨51,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13004) (by norm_num)
        (q := 1 - (cell13004 ⟨52,by decide⟩).lower)
        (by norm_num [cell13004]) (by norm_num [cell13004])
      exact ⟨E.1,E.2.trans (by norm_num [cell13004])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13004

/-! Source-cell containment and simple scalar guards at 13004. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13004)
open BstLean.Part268 (cell13004)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13004 ⟨10,by decide⟩).lower ∧ (cell13004 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13004 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13004 ⟨11,by decide⟩).lower ∧ (cell13004 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13004 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13004 ⟨12,by decide⟩).lower ∧ (cell13004 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13004 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13004 ⟨13,by decide⟩).lower ∧ (cell13004 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13004 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13004 ⟨14,by decide⟩).lower ∧ (cell13004 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13004 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13004 ⟨15,by decide⟩).lower ∧ (cell13004 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13004 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13004 ⟨16,by decide⟩).lower ∧ (cell13004 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13004 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13004 ⟨17,by decide⟩).lower ∧ (cell13004 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13004 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13004 ⟨18,by decide⟩).lower ∧ (cell13004 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13004 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13004 ⟨19,by decide⟩).lower ∧ (cell13004 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13004 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13004 ⟨20,by decide⟩).lower ∧ (cell13004 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13004 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13004 ⟨21,by decide⟩).lower ∧ (cell13004 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13004 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13004 ⟨22,by decide⟩).lower ∧ (cell13004 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13004 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13004 ⟨23,by decide⟩).lower ∧ (cell13004 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13004 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13004 ⟨24,by decide⟩).lower ∧ (cell13004 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13004 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13004 ⟨25,by decide⟩).lower ∧ (cell13004 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13004 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13004 ⟨26,by decide⟩).lower ∧ (cell13004 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13004 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13004 ⟨27,by decide⟩).lower ∧ (cell13004 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13004 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13004 ⟨28,by decide⟩).lower ∧ (cell13004 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13004 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13004 ⟨29,by decide⟩).lower ∧ (cell13004 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13004 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13004 ⟨30,by decide⟩).lower ∧ (cell13004 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13004 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13004 ⟨31,by decide⟩).lower ∧ (cell13004 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13004 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13004 ⟨32,by decide⟩).lower ∧ (cell13004 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13004 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13004 ⟨33,by decide⟩).lower ∧ (cell13004 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13004 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13004 ⟨34,by decide⟩).lower ∧ (cell13004 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13004 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13004 ⟨35,by decide⟩).lower ∧ (cell13004 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13004 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13004 ⟨36,by decide⟩).lower ∧ (cell13004 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13004 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13004 ⟨37,by decide⟩).lower ∧ (cell13004 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13004 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13004 ⟨38,by decide⟩).lower ∧ (cell13004 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13004 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13004 ⟨39,by decide⟩).lower ∧ (cell13004 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13004 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13004 ⟨40,by decide⟩).lower ∧ (cell13004 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13004 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13004 ⟨41,by decide⟩).lower ∧ (cell13004 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13004 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13004 ⟨42,by decide⟩).lower ∧ (cell13004 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13004 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13004 ⟨43,by decide⟩).lower ∧ (cell13004 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13004 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13004 ⟨44,by decide⟩).lower ∧ (cell13004 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13004 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13004 ⟨45,by decide⟩).lower ∧ (cell13004 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13004 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13004 ⟨46,by decide⟩).lower ∧ (cell13004 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13004 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13004 ⟨47,by decide⟩).lower ∧ (cell13004 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13004 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13004 ⟨48,by decide⟩).lower ∧ (cell13004 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13004 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13004 ⟨49,by decide⟩).lower ∧ (cell13004 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13004 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13004 ⟨50,by decide⟩).lower ∧ (cell13004 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13004 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13004 ⟨51,by decide⟩).lower ∧ (cell13004 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13004 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13004 ⟨52,by decide⟩).lower ∧ (cell13004 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13004 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13004 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13004 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13004,cell13004,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13004 i).lower ∧
    (cell13004 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13004 i).upper ≤ (0.532 : ℝ) ∧
    (cell13004 i).centre ≤ (0.1 : ℝ) ∧ (cell13004 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13004 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13004 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13004

/-! The local source numeric instances at 13004 have no network premises. -/
namespace BstLean.Part269.N13004
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13004)
open BstLean.Part268 (cell13004)

noncomputable def sourceNumerics13004 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13004 (cell13004 i)
      scalarRow13004.M scalarRow13004.H scalarRow13004.xi := by
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
    energy_allowance := scalarRow13004.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13004]
    centre_nonneg := (scalarRow13004.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13004])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13004
/-! Actual 13005 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13005 ≤ (1.035383150128 : ℝ) := by
  have hr : (114.039466852489 : ℝ) ≤ √(13005 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.039466852489 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13005 13005 (11 / 1000) ≤
    (0.008382071307 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13005) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.039466852489 : ℝ) ≤ √(13005 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13005)
  have hdiv : K / √(13005 : ℝ) ≤ K / 114.039466852489 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.039466852489 ≤ (0.008382071307 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13005.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13005 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13005 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13005 := gPlus_lower 13005
end BstLean.Part269.N13005

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13005
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035383150127 : ℝ) ≤ wn 13005 := by
  have hn : √(13005 : ℝ) ≤ 114.039466852490 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13005 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.039466852490 ≤ 2 / √(13005 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245872449 : ℝ) ≤ rhoBar 13005 BstLean.Part154.csC ∧
    rhoBar 13005 BstLean.Part154.csC ≤ 0.000245872830 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035383150127 : ℝ) / (1.295212 * 13005) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035383150128 : ℝ) / (1.29521 * 13005) := by gcongr
      _ ≤ (0.000245872830 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13005 BstLean.Part154.csC) ≤ 0.000983551774 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13005 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) ≤ 0.000187799118 ∧
    cc1 (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) ≤ 0.000119497869 ∧
    cc2 (rhoBar 13005 BstLean.Part154.csC) ≤ 0.000069369480 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13005 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13005 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13005 BstLean.Part154.csC * nuR (rhoBar 13005 BstLean.Part154.csC)) ≤ 0.000491760774 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245872830 : ℝ) * 0.000983551774 := by gcongr
      _ ≤ (0.000491760774 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13005 BstLean.Part154.csC) * nuR (rhoBar 13005 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983551774 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13005 BstLean.Part154.csC) * rhoBar 13005 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245872830 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245872830 / 2 + 0.399 * 0.000983551774 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187799118 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491760774 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119497869 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245872830 / 1.414213562 := by gcongr
      _ ≤ (0.000069369480 : ℝ) := by norm_num

end BstLean.Part269.N13005

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13005
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) ≤ 1.52308E-7 := by
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13005 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13005 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13005 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187799118 : ℝ) ^ 2 + 0.000119497869 ^ 2 + 3 * 0.000069369480 ^ 2 +
        2 * 0.797885 * 0.000187799118 * 0.000119497869 + 2 * 0.000187799118 * 0.000069369480 +
        4 * 0.797885 * 0.000119497869 * 0.000069369480 := by gcongr
    _ ≤ (1.52308E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13005 BstLean.Part154.csC Θ ≤ 0.002565511305 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13005 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13005 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13005 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035383150128 * 1.52308E-7 / (0.000245872449 : ℝ) := by gcongr
    _ ≤ 0.002565511305 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13005 BstLean.Part154.csC Θ ≤ 0.002845400631 + 0.000648263900 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13005 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13005 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035383150128 : ℝ) * ((2 * Θ * 0.000245872830 +
        (6863 / 10000) * 0.000245872830 * 13005 * 0.000983551774) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002845400631 + 0.000648263900 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13005 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13005 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13005 0.011 Θ ∧ gammaRatio 13005 0.011 Θ ≤ 0.000084524721 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13005 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035383150128 : ℝ) * 0.525 / ((1 - 0.011) * 13005) := by gcongr
      _ ≤ (0.000084524721 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13005 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13005 0.011 Θ) :=
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
    badAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13005 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13005 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13005 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13005 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13005 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13005 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13005 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13005 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13005 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13005 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035383150128 : ℝ) * 13005 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003228110392 + 0.003213775205 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13005

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13005
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13005 BstLean.Part154.csC) (piBar (rhoBar 13005 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13005 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13005 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13005 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13005 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13005 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13005 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13005 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13005 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13005 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13005 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051858582812 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13005) ≤ 0.010472142795 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13005 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035383150128)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010472142795 + 2 * 0.737676 / 13005) := by gcongr
    _ ≤ (0.051858582812 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13005 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13005

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13005
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517037816 : ℝ) ≤ plow 13005 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13005) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421942375)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346893436) : eMP 13005 0.011 xi bn ≤ 0.001159949142 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13005 : ℝ) * (1 - 0.011))) ≤ 0.000573572413 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346893436 / (13005 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573572413 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573572413 : ℝ) + 3.141593 * 0.052421942375 / (13005 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159949142 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421942375)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346893436) : PiBarMP 13005 12 0.011 xi bn ≤ 0.159329940231 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13005 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036700046812 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.410515385479 : ℝ) ≤ √((13005 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.039466852489 : ℝ) ≤ √(13005 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13005) ≤ 0.122171811631 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036700046812 + 0.052421942375 * 1.772454 / (2 * (113.410515385479 : ℝ))) * (1 + 0.001159949142) +
        8 / (13005 * 114.039466852489) + 0.122171811631 := by gcongr
    _ ≤ (0.159329940231 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421942375)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346893436) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280816968496) :
    parallelOracle 13005 0.011 xi bn cd ≤ 0.160296763314 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13005 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13005 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517037816 : ℝ) ≤ plow 13005 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.039466852489 : ℝ) ≤ √(13005 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280816968496 : ℝ) / (2 * 0.560517037816 * 114.039466852489)) * 0.159329940231 +
        0.280816968496 ^ 2 / (2 * 0.560517037816 * 114.039466852489) := by gcongr
    _ ≤ (0.160296763314 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421942375) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346893436)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280816968496) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13005 13005 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517037816 : ℝ) ≤ plow 13005 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.039466852489 : ℝ) ≤ √(13005 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13005 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13005 Θ 1.22 ≤ 0.011628434757 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.039466852489 := by gcongr <;> linarith
      _ ≤ (0.011628434757 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13005 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13005 13005 0.011 ≤ 0.008382071307 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13005 13005 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13005 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13005 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13005 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13005 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160296763314 + 0.011628434757 + (0.008382071307 : ℝ) *
        (1 + 2 * (0.280816968496 + 0.011628434757) / (0.560517037816 * 114.039466852489))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13005]

end BstLean.Part269.N13005

/-! The original eight local profiles supply actual 13005 moment certificates. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13005 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052421942375 ∧
    0 ≤ bN 13005 BstLean.Part154.csC (groupTheta g) ∧ bN 13005 BstLean.Part154.csC (groupTheta g) ≤ 0.001346893436 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13005 13005 0.011
      (momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13005 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13005 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13005 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228958385684 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13005 0.011
      (momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13005 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13005
/-! The actual computed-centre upper energy formula at 13005. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13005

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13005)
open BstLean.Part268 (cell13005)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084647031850
  | 2 => 0.085575532721
  | 3 => 0.086500216409
  | 4 => 0.087422041123
  | 5 => 0.088342179380
  | 6 => 0.089262051503
  | 7 => 0.090183362609
  | 8 => 0.091108143152
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13005 13005 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13005 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13005

/-! Actual upper energy certificates on all 43 source endpoints at 13005. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13005)
open BstLean.Part268 (cell13005)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13005 (gMinus 13005) (1 - (cell13005 i).lower) ≤ 1 ∧
    energyUpper 13005 (gMinus 13005) (BstLean.Part211.gPlus 13005)
      (finiteEnergy 13005 13005 0.011) (1 - (cell13005 i).lower) ≤
      (cell13005 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨10,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨11,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨12,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨13,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨14,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨15,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨16,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨17,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨18,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨19,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨20,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨21,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨22,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨23,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨24,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨25,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨26,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨27,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨28,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨29,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨30,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨31,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨32,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨33,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨34,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨35,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨36,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨37,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨38,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨39,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨40,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨41,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨42,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨43,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨44,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨45,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨46,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨47,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨48,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨49,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨50,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨51,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13005) (by norm_num)
        (q := 1 - (cell13005 ⟨52,by decide⟩).lower)
        (by norm_num [cell13005]) (by norm_num [cell13005])
      exact ⟨E.1,E.2.trans (by norm_num [cell13005])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13005

/-! Source-cell containment and simple scalar guards at 13005. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13005)
open BstLean.Part268 (cell13005)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13005 ⟨10,by decide⟩).lower ∧ (cell13005 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13005 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13005 ⟨11,by decide⟩).lower ∧ (cell13005 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13005 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13005 ⟨12,by decide⟩).lower ∧ (cell13005 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13005 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13005 ⟨13,by decide⟩).lower ∧ (cell13005 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13005 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13005 ⟨14,by decide⟩).lower ∧ (cell13005 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13005 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13005 ⟨15,by decide⟩).lower ∧ (cell13005 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13005 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13005 ⟨16,by decide⟩).lower ∧ (cell13005 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13005 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13005 ⟨17,by decide⟩).lower ∧ (cell13005 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13005 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13005 ⟨18,by decide⟩).lower ∧ (cell13005 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13005 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13005 ⟨19,by decide⟩).lower ∧ (cell13005 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13005 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13005 ⟨20,by decide⟩).lower ∧ (cell13005 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13005 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13005 ⟨21,by decide⟩).lower ∧ (cell13005 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13005 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13005 ⟨22,by decide⟩).lower ∧ (cell13005 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13005 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13005 ⟨23,by decide⟩).lower ∧ (cell13005 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13005 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13005 ⟨24,by decide⟩).lower ∧ (cell13005 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13005 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13005 ⟨25,by decide⟩).lower ∧ (cell13005 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13005 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13005 ⟨26,by decide⟩).lower ∧ (cell13005 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13005 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13005 ⟨27,by decide⟩).lower ∧ (cell13005 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13005 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13005 ⟨28,by decide⟩).lower ∧ (cell13005 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13005 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13005 ⟨29,by decide⟩).lower ∧ (cell13005 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13005 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13005 ⟨30,by decide⟩).lower ∧ (cell13005 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13005 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13005 ⟨31,by decide⟩).lower ∧ (cell13005 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13005 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13005 ⟨32,by decide⟩).lower ∧ (cell13005 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13005 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13005 ⟨33,by decide⟩).lower ∧ (cell13005 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13005 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13005 ⟨34,by decide⟩).lower ∧ (cell13005 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13005 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13005 ⟨35,by decide⟩).lower ∧ (cell13005 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13005 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13005 ⟨36,by decide⟩).lower ∧ (cell13005 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13005 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13005 ⟨37,by decide⟩).lower ∧ (cell13005 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13005 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13005 ⟨38,by decide⟩).lower ∧ (cell13005 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13005 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13005 ⟨39,by decide⟩).lower ∧ (cell13005 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13005 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13005 ⟨40,by decide⟩).lower ∧ (cell13005 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13005 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13005 ⟨41,by decide⟩).lower ∧ (cell13005 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13005 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13005 ⟨42,by decide⟩).lower ∧ (cell13005 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13005 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13005 ⟨43,by decide⟩).lower ∧ (cell13005 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13005 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13005 ⟨44,by decide⟩).lower ∧ (cell13005 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13005 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13005 ⟨45,by decide⟩).lower ∧ (cell13005 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13005 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13005 ⟨46,by decide⟩).lower ∧ (cell13005 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13005 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13005 ⟨47,by decide⟩).lower ∧ (cell13005 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13005 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13005 ⟨48,by decide⟩).lower ∧ (cell13005 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13005 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13005 ⟨49,by decide⟩).lower ∧ (cell13005 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13005 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13005 ⟨50,by decide⟩).lower ∧ (cell13005 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13005 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13005 ⟨51,by decide⟩).lower ∧ (cell13005 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13005 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13005 ⟨52,by decide⟩).lower ∧ (cell13005 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13005 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13005 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13005 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13005,cell13005,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13005 i).lower ∧
    (cell13005 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13005 i).upper ≤ (0.532 : ℝ) ∧
    (cell13005 i).centre ≤ (0.1 : ℝ) ∧ (cell13005 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13005 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13005 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13005

/-! The local source numeric instances at 13005 have no network premises. -/
namespace BstLean.Part269.N13005
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13005)
open BstLean.Part268 (cell13005)

noncomputable def sourceNumerics13005 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13005 (cell13005 i)
      scalarRow13005.M scalarRow13005.H scalarRow13005.xi := by
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
    energy_allowance := scalarRow13005.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13005]
    centre_nonneg := (scalarRow13005.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13005])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13005
/-! Actual 13006 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13006 ≤ (1.035381778015 : ℝ) := by
  have hr : (114.043851215223 : ℝ) ≤ √(13006 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.043851215223 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13006 13006 (11 / 1000) ≤
    (0.008381749059 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13006) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.043851215223 : ℝ) ≤ √(13006 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13006)
  have hdiv : K / √(13006 : ℝ) ≤ K / 114.043851215223 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.043851215223 ≤ (0.008381749059 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13006.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13006 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13006 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13006 := gPlus_lower 13006
end BstLean.Part269.N13006

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13006
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035381778014 : ℝ) ≤ wn 13006 := by
  have hn : √(13006 : ℝ) ≤ 114.043851215224 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13006 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.043851215224 ≤ 2 / √(13006 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245853219 : ℝ) ≤ rhoBar 13006 BstLean.Part154.csC ∧
    rhoBar 13006 BstLean.Part154.csC ≤ 0.000245853600 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035381778014 : ℝ) / (1.295212 * 13006) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035381778015 : ℝ) / (1.29521 * 13006) := by gcongr
      _ ≤ (0.000245853600 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13006 BstLean.Part154.csC) ≤ 0.000983474844 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13006 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) ≤ 0.000187784429 ∧
    cc1 (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) ≤ 0.000119488522 ∧
    cc2 (rhoBar 13006 BstLean.Part154.csC) ≤ 0.000069364055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13006 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13006 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13006 BstLean.Part154.csC * nuR (rhoBar 13006 BstLean.Part154.csC)) ≤ 0.000491722311 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245853600 : ℝ) * 0.000983474844 := by gcongr
      _ ≤ (0.000491722311 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13006 BstLean.Part154.csC) * nuR (rhoBar 13006 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983474844 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13006 BstLean.Part154.csC) * rhoBar 13006 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245853600 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245853600 / 2 + 0.399 * 0.000983474844 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187784429 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491722311 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119488522 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245853600 / 1.414213562 := by gcongr
      _ ≤ (0.000069364055 : ℝ) := by norm_num

end BstLean.Part269.N13006

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13006
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) ≤ 1.52284E-7 := by
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13006 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13006 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13006 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187784429 : ℝ) ^ 2 + 0.000119488522 ^ 2 + 3 * 0.000069364055 ^ 2 +
        2 * 0.797885 * 0.000187784429 * 0.000119488522 + 2 * 0.000187784429 * 0.000069364055 +
        4 * 0.797885 * 0.000119488522 * 0.000069364055 := by gcongr
    _ ≤ (1.52284E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13006 BstLean.Part154.csC Θ ≤ 0.002565304280 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13006 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13006 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13006 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035381778015 * 1.52284E-7 / (0.000245853219 : ℝ) := by gcongr
    _ ≤ 0.002565304280 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13006 BstLean.Part154.csC Θ ≤ 0.002845170537 + 0.000648212340 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13006 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13006 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035381778015 : ℝ) * ((2 * Θ * 0.000245853600 +
        (6863 / 10000) * 0.000245853600 * 13006 * 0.000983474844) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002845170537 + 0.000648212340 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13006 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13006 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13006 0.011 Θ ∧ gammaRatio 13006 0.011 Θ ≤ 0.000084518110 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13006 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035381778015 : ℝ) * 0.525 / ((1 - 0.011) * 13006) := by gcongr
      _ ≤ (0.000084518110 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13006 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13006 0.011 Θ) :=
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
    badAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13006 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13006 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13006 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13006 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13006 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13006 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13006 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13006 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13006 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13006 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035381778015 : ℝ) * 13006 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003227880298 + 0.003213516620 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13006

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13006
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13006 BstLean.Part154.csC) (piBar (rhoBar 13006 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13006 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13006 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13006 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13006 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13006 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13006 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13006 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13006 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13006 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13006 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051856567766 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13006) ≤ 0.010471740198 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13006 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035381778015)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010471740198 + 2 * 0.737676 / 13006) := by gcongr
    _ ≤ (0.051856567766 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13006 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13006

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13006
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517080939 : ℝ) ≤ plow 13006 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13006) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421576524)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346784747) : eMP 13006 0.011 xi bn ≤ 0.001159857683 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13006 : ℝ) * (1 - 0.011))) ≤ 0.000573527220 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346784747 / (13006 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573527220 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573527220 : ℝ) + 3.141593 * 0.052421576524 / (13006 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159857683 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421576524)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346784747) : PiBarMP 13006 12 0.011 xi bn ≤ 0.159323738227 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13006 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036698566008 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.414875567537 : ℝ) ≤ √((13006 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.043851215223 : ℝ) ≤ √(13006 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13006) ≤ 0.122167114793 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036698566008 + 0.052421576524 * 1.772454 / (2 * (113.414875567537 : ℝ))) * (1 + 0.001159857683) +
        8 / (13006 * 114.043851215223) + 0.122167114793 := by gcongr
    _ ≤ (0.159323738227 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421576524)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346784747) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280814154503) :
    parallelOracle 13006 0.011 xi bn cd ≤ 0.160290494575 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13006 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13006 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517080939 : ℝ) ≤ plow 13006 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.043851215223 : ℝ) ≤ √(13006 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280814154503 : ℝ) / (2 * 0.560517080939 * 114.043851215223)) * 0.159323738227 +
        0.280814154503 ^ 2 / (2 * 0.560517080939 * 114.043851215223) := by gcongr
    _ ≤ (0.160290494575 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421576524) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346784747)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280814154503) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13006 13006 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517080939 : ℝ) ≤ plow 13006 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.043851215223 : ℝ) ≤ √(13006 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13006 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13006 Θ 1.22 ≤ 0.011627987708 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.043851215223 := by gcongr <;> linarith
      _ ≤ (0.011627987708 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13006 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13006 13006 0.011 ≤ 0.008381749059 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13006 13006 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13006 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13006 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13006 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13006 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160290494575 + 0.011627987708 + (0.008381749059 : ℝ) *
        (1 + 2 * (0.280814154503 + 0.011627987708) / (0.560517080939 * 114.043851215223))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13006]

end BstLean.Part269.N13006

/-! The original eight local profiles supply actual 13006 moment certificates. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13006 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052421576524 ∧
    0 ≤ bN 13006 BstLean.Part154.csC (groupTheta g) ∧ bN 13006 BstLean.Part154.csC (groupTheta g) ≤ 0.001346784747 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13006 13006 0.011
      (momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13006 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13006 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13006 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228957586737 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13006 0.011
      (momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13006 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13006
/-! The actual computed-centre upper energy formula at 13006. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13006

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13006)
open BstLean.Part268 (cell13006)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084644417666
  | 2 => 0.085572884131
  | 3 => 0.086497528191
  | 4 => 0.087419306833
  | 5 => 0.088339391125
  | 6 => 0.089259199692
  | 7 => 0.090180435668
  | 8 => 0.091105127207
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13006 13006 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13006 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13006

/-! Actual upper energy certificates on all 43 source endpoints at 13006. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13006)
open BstLean.Part268 (cell13006)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13006 (gMinus 13006) (1 - (cell13006 i).lower) ≤ 1 ∧
    energyUpper 13006 (gMinus 13006) (BstLean.Part211.gPlus 13006)
      (finiteEnergy 13006 13006 0.011) (1 - (cell13006 i).lower) ≤
      (cell13006 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨10,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨11,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨12,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨13,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨14,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨15,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨16,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨17,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨18,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨19,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨20,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨21,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨22,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨23,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨24,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨25,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨26,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨27,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨28,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨29,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨30,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨31,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨32,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨33,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨34,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨35,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨36,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨37,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨38,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨39,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨40,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨41,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨42,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨43,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨44,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨45,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨46,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨47,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨48,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨49,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨50,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨51,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13006) (by norm_num)
        (q := 1 - (cell13006 ⟨52,by decide⟩).lower)
        (by norm_num [cell13006]) (by norm_num [cell13006])
      exact ⟨E.1,E.2.trans (by norm_num [cell13006])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13006

/-! Source-cell containment and simple scalar guards at 13006. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13006)
open BstLean.Part268 (cell13006)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13006 ⟨10,by decide⟩).lower ∧ (cell13006 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13006 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13006 ⟨11,by decide⟩).lower ∧ (cell13006 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13006 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13006 ⟨12,by decide⟩).lower ∧ (cell13006 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13006 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13006 ⟨13,by decide⟩).lower ∧ (cell13006 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13006 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13006 ⟨14,by decide⟩).lower ∧ (cell13006 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13006 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13006 ⟨15,by decide⟩).lower ∧ (cell13006 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13006 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13006 ⟨16,by decide⟩).lower ∧ (cell13006 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13006 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13006 ⟨17,by decide⟩).lower ∧ (cell13006 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13006 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13006 ⟨18,by decide⟩).lower ∧ (cell13006 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13006 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13006 ⟨19,by decide⟩).lower ∧ (cell13006 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13006 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13006 ⟨20,by decide⟩).lower ∧ (cell13006 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13006 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13006 ⟨21,by decide⟩).lower ∧ (cell13006 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13006 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13006 ⟨22,by decide⟩).lower ∧ (cell13006 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13006 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13006 ⟨23,by decide⟩).lower ∧ (cell13006 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13006 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13006 ⟨24,by decide⟩).lower ∧ (cell13006 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13006 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13006 ⟨25,by decide⟩).lower ∧ (cell13006 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13006 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13006 ⟨26,by decide⟩).lower ∧ (cell13006 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13006 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13006 ⟨27,by decide⟩).lower ∧ (cell13006 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13006 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13006 ⟨28,by decide⟩).lower ∧ (cell13006 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13006 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13006 ⟨29,by decide⟩).lower ∧ (cell13006 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13006 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13006 ⟨30,by decide⟩).lower ∧ (cell13006 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13006 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13006 ⟨31,by decide⟩).lower ∧ (cell13006 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13006 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13006 ⟨32,by decide⟩).lower ∧ (cell13006 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13006 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13006 ⟨33,by decide⟩).lower ∧ (cell13006 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13006 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13006 ⟨34,by decide⟩).lower ∧ (cell13006 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13006 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13006 ⟨35,by decide⟩).lower ∧ (cell13006 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13006 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13006 ⟨36,by decide⟩).lower ∧ (cell13006 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13006 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13006 ⟨37,by decide⟩).lower ∧ (cell13006 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13006 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13006 ⟨38,by decide⟩).lower ∧ (cell13006 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13006 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13006 ⟨39,by decide⟩).lower ∧ (cell13006 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13006 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13006 ⟨40,by decide⟩).lower ∧ (cell13006 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13006 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13006 ⟨41,by decide⟩).lower ∧ (cell13006 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13006 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13006 ⟨42,by decide⟩).lower ∧ (cell13006 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13006 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13006 ⟨43,by decide⟩).lower ∧ (cell13006 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13006 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13006 ⟨44,by decide⟩).lower ∧ (cell13006 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13006 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13006 ⟨45,by decide⟩).lower ∧ (cell13006 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13006 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13006 ⟨46,by decide⟩).lower ∧ (cell13006 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13006 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13006 ⟨47,by decide⟩).lower ∧ (cell13006 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13006 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13006 ⟨48,by decide⟩).lower ∧ (cell13006 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13006 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13006 ⟨49,by decide⟩).lower ∧ (cell13006 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13006 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13006 ⟨50,by decide⟩).lower ∧ (cell13006 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13006 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13006 ⟨51,by decide⟩).lower ∧ (cell13006 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13006 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13006 ⟨52,by decide⟩).lower ∧ (cell13006 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13006 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13006 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13006 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13006,cell13006,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13006 i).lower ∧
    (cell13006 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13006 i).upper ≤ (0.532 : ℝ) ∧
    (cell13006 i).centre ≤ (0.1 : ℝ) ∧ (cell13006 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13006 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13006 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13006

/-! The local source numeric instances at 13006 have no network premises. -/
namespace BstLean.Part269.N13006
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13006)
open BstLean.Part268 (cell13006)

noncomputable def sourceNumerics13006 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13006 (cell13006 i)
      scalarRow13006.M scalarRow13006.H scalarRow13006.xi := by
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
    energy_allowance := scalarRow13006.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13006]
    centre_nonneg := (scalarRow13006.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13006])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13006
/-! Actual 13007 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13007 ≤ (1.035380406062 : ℝ) := by
  have hr : (114.048235409409 : ℝ) ≤ √(13007 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.048235409409 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13007 13007 (11 / 1000) ≤
    (0.008381426849 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13007) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.048235409409 : ℝ) ≤ √(13007 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13007)
  have hdiv : K / √(13007 : ℝ) ≤ K / 114.048235409409 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.048235409409 ≤ (0.008381426849 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13007.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13007 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13007 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13007 := gPlus_lower 13007
end BstLean.Part269.N13007

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13007
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035380406061 : ℝ) ≤ wn 13007 := by
  have hn : √(13007 : ℝ) ≤ 114.048235409410 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13007 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.048235409410 ≤ 2 / √(13007 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245833992 : ℝ) ≤ rhoBar 13007 BstLean.Part154.csC ∧
    rhoBar 13007 BstLean.Part154.csC ≤ 0.000245834372 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035380406061 : ℝ) / (1.295212 * 13007) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035380406062 : ℝ) / (1.29521 * 13007) := by gcongr
      _ ≤ (0.000245834372 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13007 BstLean.Part154.csC) ≤ 0.000983397923 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13007 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) ≤ 0.000187769742 ∧
    cc1 (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) ≤ 0.000119479177 ∧
    cc2 (rhoBar 13007 BstLean.Part154.csC) ≤ 0.000069358630 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13007 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13007 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13007 BstLean.Part154.csC * nuR (rhoBar 13007 BstLean.Part154.csC)) ≤ 0.000491683853 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245834372 : ℝ) * 0.000983397923 := by gcongr
      _ ≤ (0.000491683853 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13007 BstLean.Part154.csC) * nuR (rhoBar 13007 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983397923 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13007 BstLean.Part154.csC) * rhoBar 13007 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245834372 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245834372 / 2 + 0.399 * 0.000983397923 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187769742 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491683853 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119479177 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245834372 / 1.414213562 := by gcongr
      _ ≤ (0.000069358630 : ℝ) := by norm_num

end BstLean.Part269.N13007

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13007
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) ≤ 1.52260E-7 := by
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13007 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13007 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13007 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187769742 : ℝ) ^ 2 + 0.000119479177 ^ 2 + 3 * 0.000069358630 ^ 2 +
        2 * 0.797885 * 0.000187769742 * 0.000119479177 + 2 * 0.000187769742 * 0.000069358630 +
        4 * 0.797885 * 0.000119479177 * 0.000069358630 := by gcongr
    _ ≤ (1.52260E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13007 BstLean.Part154.csC Θ ≤ 0.002565097192 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13007 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13007 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13007 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035380406062 * 1.52260E-7 / (0.000245833992 : ℝ) := by gcongr
    _ ≤ 0.002565097192 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13007 BstLean.Part154.csC Θ ≤ 0.002844940460 + 0.000648160785 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13007 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13007 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035380406062 : ℝ) * ((2 * Θ * 0.000245834372 +
        (6863 / 10000) * 0.000245834372 * 13007 * 0.000983397923) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002844940460 + 0.000648160785 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13007 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13007 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13007 0.011 Θ ∧ gammaRatio 13007 0.011 Θ ≤ 0.000084511500 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13007 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035380406062 : ℝ) * 0.525 / ((1 - 0.011) * 13007) := by gcongr
      _ ≤ (0.000084511500 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13007 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13007 0.011 Θ) :=
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
    badAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13007 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13007 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13007 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13007 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13007 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13007 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13007 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13007 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13007 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13007 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035380406062 : ℝ) * 13007 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003227650221 + 0.003213257977 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13007

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13007
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13007 BstLean.Part154.csC) (piBar (rhoBar 13007 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13007 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13007 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13007 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13007 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13007 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13007 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13007 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13007 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13007 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13007 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051854552956 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13007) ≤ 0.010471337648 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13007 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035380406062)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010471337648 + 2 * 0.737676 / 13007) := by gcongr
    _ ≤ (0.051854552956 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13007 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13007

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13007
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517124056 : ℝ) ≤ plow 13007 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13007) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421210659)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346676026) : eMP 13007 0.011 xi bn ≤ 0.001159766217 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13007 : ℝ) * (1 - 0.011))) ≤ 0.000573482024 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346676026 / (13007 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573482024 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573482024 : ℝ) + 3.141593 * 0.052421210659 / (13007 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159766217 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421210659)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346676026) : PiBarMP 13007 12 0.011 xi bn ≤ 0.159317536269 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13007 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036697084708 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.419235581977 : ℝ) ≤ √((13007 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.048235409409 : ℝ) ≤ √(13007 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13007) ≤ 0.122162418496 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036697084708 + 0.052421210659 * 1.772454 / (2 * (113.419235581977 : ℝ))) * (1 + 0.001159766217) +
        8 / (13007 * 114.048235409409) + 0.122162418496 := by gcongr
    _ ≤ (0.159317536269 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421210659)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346676026) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280811340711) :
    parallelOracle 13007 0.011 xi bn cd ≤ 0.160284225891 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13007 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13007 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517124056 : ℝ) ≤ plow 13007 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.048235409409 : ℝ) ≤ √(13007 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280811340711 : ℝ) / (2 * 0.560517124056 * 114.048235409409)) * 0.159317536269 +
        0.280811340711 ^ 2 / (2 * 0.560517124056 * 114.048235409409) := by gcongr
    _ ≤ (0.160284225891 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052421210659) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346676026)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280811340711) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13007 13007 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517124056 : ℝ) ≤ plow 13007 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.048235409409 : ℝ) ≤ √(13007 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13007 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13007 Θ 1.22 ≤ 0.011627540709 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.048235409409 := by gcongr <;> linarith
      _ ≤ (0.011627540709 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13007 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13007 13007 0.011 ≤ 0.008381426849 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13007 13007 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13007 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13007 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13007 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13007 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160284225891 + 0.011627540709 + (0.008381426849 : ℝ) *
        (1 + 2 * (0.280811340711 + 0.011627540709) / (0.560517124056 * 114.048235409409))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13007]

end BstLean.Part269.N13007

/-! The original eight local profiles supply actual 13007 moment certificates. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13007 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052421210659 ∧
    0 ≤ bN 13007 BstLean.Part154.csC (groupTheta g) ∧ bN 13007 BstLean.Part154.csC (groupTheta g) ≤ 0.001346676026 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13007 13007 0.011
      (momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13007 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13007 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13007 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228956787755 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13007 0.011
      (momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13007 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13007
/-! The actual computed-centre upper energy formula at 13007. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13007

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13007)
open BstLean.Part268 (cell13007)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084641804285
  | 2 => 0.085570236372
  | 3 => 0.086494840841
  | 4 => 0.087416573453
  | 5 => 0.088336603833
  | 6 => 0.089256348910
  | 7 => 0.090177509834
  | 8 => 0.091102112463
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13007 13007 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13007 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13007

/-! Actual upper energy certificates on all 43 source endpoints at 13007. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13007)
open BstLean.Part268 (cell13007)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13007 (gMinus 13007) (1 - (cell13007 i).lower) ≤ 1 ∧
    energyUpper 13007 (gMinus 13007) (BstLean.Part211.gPlus 13007)
      (finiteEnergy 13007 13007 0.011) (1 - (cell13007 i).lower) ≤
      (cell13007 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨10,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨11,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨12,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨13,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨14,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨15,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨16,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨17,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨18,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨19,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨20,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨21,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨22,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨23,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨24,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨25,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨26,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨27,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨28,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨29,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨30,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨31,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨32,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨33,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨34,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨35,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨36,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨37,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨38,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨39,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨40,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨41,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨42,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨43,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨44,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨45,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨46,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨47,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨48,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨49,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨50,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨51,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13007) (by norm_num)
        (q := 1 - (cell13007 ⟨52,by decide⟩).lower)
        (by norm_num [cell13007]) (by norm_num [cell13007])
      exact ⟨E.1,E.2.trans (by norm_num [cell13007])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13007

/-! Source-cell containment and simple scalar guards at 13007. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13007)
open BstLean.Part268 (cell13007)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13007 ⟨10,by decide⟩).lower ∧ (cell13007 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13007 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13007 ⟨11,by decide⟩).lower ∧ (cell13007 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13007 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13007 ⟨12,by decide⟩).lower ∧ (cell13007 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13007 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13007 ⟨13,by decide⟩).lower ∧ (cell13007 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13007 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13007 ⟨14,by decide⟩).lower ∧ (cell13007 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13007 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13007 ⟨15,by decide⟩).lower ∧ (cell13007 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13007 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13007 ⟨16,by decide⟩).lower ∧ (cell13007 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13007 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13007 ⟨17,by decide⟩).lower ∧ (cell13007 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13007 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13007 ⟨18,by decide⟩).lower ∧ (cell13007 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13007 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13007 ⟨19,by decide⟩).lower ∧ (cell13007 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13007 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13007 ⟨20,by decide⟩).lower ∧ (cell13007 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13007 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13007 ⟨21,by decide⟩).lower ∧ (cell13007 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13007 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13007 ⟨22,by decide⟩).lower ∧ (cell13007 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13007 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13007 ⟨23,by decide⟩).lower ∧ (cell13007 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13007 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13007 ⟨24,by decide⟩).lower ∧ (cell13007 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13007 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13007 ⟨25,by decide⟩).lower ∧ (cell13007 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13007 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13007 ⟨26,by decide⟩).lower ∧ (cell13007 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13007 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13007 ⟨27,by decide⟩).lower ∧ (cell13007 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13007 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13007 ⟨28,by decide⟩).lower ∧ (cell13007 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13007 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13007 ⟨29,by decide⟩).lower ∧ (cell13007 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13007 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13007 ⟨30,by decide⟩).lower ∧ (cell13007 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13007 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13007 ⟨31,by decide⟩).lower ∧ (cell13007 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13007 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13007 ⟨32,by decide⟩).lower ∧ (cell13007 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13007 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13007 ⟨33,by decide⟩).lower ∧ (cell13007 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13007 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13007 ⟨34,by decide⟩).lower ∧ (cell13007 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13007 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13007 ⟨35,by decide⟩).lower ∧ (cell13007 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13007 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13007 ⟨36,by decide⟩).lower ∧ (cell13007 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13007 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13007 ⟨37,by decide⟩).lower ∧ (cell13007 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13007 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13007 ⟨38,by decide⟩).lower ∧ (cell13007 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13007 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13007 ⟨39,by decide⟩).lower ∧ (cell13007 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13007 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13007 ⟨40,by decide⟩).lower ∧ (cell13007 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13007 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13007 ⟨41,by decide⟩).lower ∧ (cell13007 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13007 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13007 ⟨42,by decide⟩).lower ∧ (cell13007 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13007 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13007 ⟨43,by decide⟩).lower ∧ (cell13007 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13007 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13007 ⟨44,by decide⟩).lower ∧ (cell13007 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13007 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13007 ⟨45,by decide⟩).lower ∧ (cell13007 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13007 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13007 ⟨46,by decide⟩).lower ∧ (cell13007 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13007 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13007 ⟨47,by decide⟩).lower ∧ (cell13007 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13007 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13007 ⟨48,by decide⟩).lower ∧ (cell13007 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13007 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13007 ⟨49,by decide⟩).lower ∧ (cell13007 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13007 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13007 ⟨50,by decide⟩).lower ∧ (cell13007 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13007 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13007 ⟨51,by decide⟩).lower ∧ (cell13007 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13007 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13007 ⟨52,by decide⟩).lower ∧ (cell13007 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13007 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13007 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13007 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13007,cell13007,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13007 i).lower ∧
    (cell13007 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13007 i).upper ≤ (0.532 : ℝ) ∧
    (cell13007 i).centre ≤ (0.1 : ℝ) ∧ (cell13007 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13007 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13007 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13007

/-! The local source numeric instances at 13007 have no network premises. -/
namespace BstLean.Part269.N13007
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13007)
open BstLean.Part268 (cell13007)

noncomputable def sourceNumerics13007 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13007 (cell13007 i)
      scalarRow13007.M scalarRow13007.H scalarRow13007.xi := by
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
    energy_allowance := scalarRow13007.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13007]
    centre_nonneg := (scalarRow13007.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13007])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13007
/-! Actual 13008 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13008 ≤ (1.035379034267 : ℝ) := by
  have hr : (114.052619435066 : ℝ) ≤ √(13008 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.052619435066 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13008 13008 (11 / 1000) ≤
    (0.008381104676 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13008) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.052619435066 : ℝ) ≤ √(13008 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13008)
  have hdiv : K / √(13008 : ℝ) ≤ K / 114.052619435066 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.052619435066 ≤ (0.008381104676 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13008.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13008 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13008 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13008 := gPlus_lower 13008
end BstLean.Part269.N13008

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13008
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035379034266 : ℝ) ≤ wn 13008 := by
  have hn : √(13008 : ℝ) ≤ 114.052619435067 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13008 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.052619435067 ≤ 2 / √(13008 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245814767 : ℝ) ≤ rhoBar 13008 BstLean.Part154.csC ∧
    rhoBar 13008 BstLean.Part154.csC ≤ 0.000245815148 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035379034266 : ℝ) / (1.295212 * 13008) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035379034267 : ℝ) / (1.29521 * 13008) := by gcongr
      _ ≤ (0.000245815148 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13008 BstLean.Part154.csC) ≤ 0.000983321018 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13008 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) ≤ 0.000187755058 ∧
    cc1 (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) ≤ 0.000119469833 ∧
    cc2 (rhoBar 13008 BstLean.Part154.csC) ≤ 0.000069353206 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13008 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13008 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13008 BstLean.Part154.csC * nuR (rhoBar 13008 BstLean.Part154.csC)) ≤ 0.000491645403 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245815148 : ℝ) * 0.000983321018 := by gcongr
      _ ≤ (0.000491645403 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13008 BstLean.Part154.csC) * nuR (rhoBar 13008 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983321018 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13008 BstLean.Part154.csC) * rhoBar 13008 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245815148 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245815148 / 2 + 0.399 * 0.000983321018 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187755058 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491645403 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119469833 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245815148 / 1.414213562 := by gcongr
      _ ≤ (0.000069353206 : ℝ) := by norm_num

end BstLean.Part269.N13008

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13008
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) ≤ 1.52237E-7 := by
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13008 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13008 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13008 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187755058 : ℝ) ^ 2 + 0.000119469833 ^ 2 + 3 * 0.000069353206 ^ 2 +
        2 * 0.797885 * 0.000187755058 * 0.000119469833 + 2 * 0.000187755058 * 0.000069353206 +
        4 * 0.797885 * 0.000119469833 * 0.000069353206 := by gcongr
    _ ≤ (1.52237E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13008 BstLean.Part154.csC Θ ≤ 0.002564906901 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13008 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13008 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13008 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035379034267 * 1.52237E-7 / (0.000245814767 : ℝ) := by gcongr
    _ ≤ 0.002564906901 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13008 BstLean.Part154.csC Θ ≤ 0.002844710442 + 0.000648109241 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13008 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13008 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035379034267 : ℝ) * ((2 * Θ * 0.000245815148 +
        (6863 / 10000) * 0.000245815148 * 13008 * 0.000983321018) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002844710442 + 0.000648109241 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13008 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13008 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13008 0.011 Θ ∧ gammaRatio 13008 0.011 Θ ≤ 0.000084504891 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13008 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035379034267 : ℝ) * 0.525 / ((1 - 0.011) * 13008) := by gcongr
      _ ≤ (0.000084504891 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13008 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13008 0.011 Θ) :=
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
    badAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13008 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13008 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13008 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13008 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13008 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13008 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13008 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13008 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13008 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13008 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035379034267 : ℝ) * 13008 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003227420203 + 0.003213016142 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13008

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13008
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13008 BstLean.Part154.csC) (piBar (rhoBar 13008 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13008 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13008 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13008 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13008 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13008 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13008 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13008 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13008 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13008 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13008 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051852538379 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13008) ≤ 0.010470935144 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13008 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035379034267)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010470935144 + 2 * 0.737676 / 13008) := by gcongr
    _ ≤ (0.051852538379 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13008 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13008

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13008
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517167166 : ℝ) ≤ plow 13008 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13008) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420853678)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346576124) : eMP 13008 0.011 xi bn ≤ 0.001159678516 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13008 : ℝ) * (1 - 0.011))) ≤ 0.000573438709 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346576124 / (13008 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573438709 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573438709 : ℝ) + 3.141593 * 0.052420853678 / (13008 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159678516 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420853678)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346576124) : PiBarMP 13008 12 0.011 xi bn ≤ 0.159311455308 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13008 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036695723512 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.423595428817 : ℝ) ≤ √((13008 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.052619435066 : ℝ) ≤ √(13008 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13008) ≤ 0.122157722741 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036695723512 + 0.052420853678 * 1.772454 / (2 * (113.423595428817 : ℝ))) * (1 + 0.001159678516) +
        8 / (13008 * 114.052619435066) + 0.122157722741 := by gcongr
    _ ≤ (0.159311455308 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420853678)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346576124) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280808546551) :
    parallelOracle 13008 0.011 xi bn cd ≤ 0.160278078587 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13008 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13008 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517167166 : ℝ) ≤ plow 13008 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.052619435066 : ℝ) ≤ √(13008 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280808546551 : ℝ) / (2 * 0.560517167166 * 114.052619435066)) * 0.159311455308 +
        0.280808546551 ^ 2 / (2 * 0.560517167166 * 114.052619435066) := by gcongr
    _ ≤ (0.160278078587 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420853678) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346576124)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280808546551) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13008 13008 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517167166 : ℝ) ≤ plow 13008 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.052619435066 : ℝ) ≤ √(13008 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13008 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13008 Θ 1.22 ≤ 0.011627093763 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.052619435066 := by gcongr <;> linarith
      _ ≤ (0.011627093763 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13008 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13008 13008 0.011 ≤ 0.008381104676 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13008 13008 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13008 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13008 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13008 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13008 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160278078587 + 0.011627093763 + (0.008381104676 : ℝ) *
        (1 + 2 * (0.280808546551 + 0.011627093763) / (0.560517167166 * 114.052619435066))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13008]

end BstLean.Part269.N13008

/-! The original eight local profiles supply actual 13008 moment certificates. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13008 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052420853678 ∧
    0 ≤ bN 13008 BstLean.Part154.csC (groupTheta g) ∧ bN 13008 BstLean.Part154.csC (groupTheta g) ≤ 0.001346576124 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13008 13008 0.011
      (momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13008 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13008 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13008 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228956008172 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13008 0.011
      (momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13008 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13008
/-! The actual computed-centre upper energy formula at 13008. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13008

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13008)
open BstLean.Part268 (cell13008)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084639191706
  | 2 => 0.085567589445
  | 3 => 0.086492154356
  | 4 => 0.087413840982
  | 5 => 0.088333817504
  | 6 => 0.089253499154
  | 7 => 0.090174585106
  | 8 => 0.091099098921
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13008 13008 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13008 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13008

/-! Actual upper energy certificates on all 43 source endpoints at 13008. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13008)
open BstLean.Part268 (cell13008)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13008 (gMinus 13008) (1 - (cell13008 i).lower) ≤ 1 ∧
    energyUpper 13008 (gMinus 13008) (BstLean.Part211.gPlus 13008)
      (finiteEnergy 13008 13008 0.011) (1 - (cell13008 i).lower) ≤
      (cell13008 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨10,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨11,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨12,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨13,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨14,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨15,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨16,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨17,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨18,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨19,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨20,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨21,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨22,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨23,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨24,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨25,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨26,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨27,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨28,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨29,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨30,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨31,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨32,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨33,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨34,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨35,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨36,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨37,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨38,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨39,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨40,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨41,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨42,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨43,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨44,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨45,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨46,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨47,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨48,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨49,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨50,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨51,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13008) (by norm_num)
        (q := 1 - (cell13008 ⟨52,by decide⟩).lower)
        (by norm_num [cell13008]) (by norm_num [cell13008])
      exact ⟨E.1,E.2.trans (by norm_num [cell13008])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13008

/-! Source-cell containment and simple scalar guards at 13008. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13008)
open BstLean.Part268 (cell13008)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13008 ⟨10,by decide⟩).lower ∧ (cell13008 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13008 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13008 ⟨11,by decide⟩).lower ∧ (cell13008 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13008 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13008 ⟨12,by decide⟩).lower ∧ (cell13008 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13008 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13008 ⟨13,by decide⟩).lower ∧ (cell13008 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13008 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13008 ⟨14,by decide⟩).lower ∧ (cell13008 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13008 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13008 ⟨15,by decide⟩).lower ∧ (cell13008 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13008 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13008 ⟨16,by decide⟩).lower ∧ (cell13008 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13008 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13008 ⟨17,by decide⟩).lower ∧ (cell13008 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13008 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13008 ⟨18,by decide⟩).lower ∧ (cell13008 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13008 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13008 ⟨19,by decide⟩).lower ∧ (cell13008 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13008 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13008 ⟨20,by decide⟩).lower ∧ (cell13008 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13008 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13008 ⟨21,by decide⟩).lower ∧ (cell13008 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13008 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13008 ⟨22,by decide⟩).lower ∧ (cell13008 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13008 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13008 ⟨23,by decide⟩).lower ∧ (cell13008 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13008 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13008 ⟨24,by decide⟩).lower ∧ (cell13008 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13008 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13008 ⟨25,by decide⟩).lower ∧ (cell13008 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13008 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13008 ⟨26,by decide⟩).lower ∧ (cell13008 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13008 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13008 ⟨27,by decide⟩).lower ∧ (cell13008 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13008 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13008 ⟨28,by decide⟩).lower ∧ (cell13008 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13008 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13008 ⟨29,by decide⟩).lower ∧ (cell13008 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13008 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13008 ⟨30,by decide⟩).lower ∧ (cell13008 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13008 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13008 ⟨31,by decide⟩).lower ∧ (cell13008 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13008 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13008 ⟨32,by decide⟩).lower ∧ (cell13008 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13008 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13008 ⟨33,by decide⟩).lower ∧ (cell13008 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13008 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13008 ⟨34,by decide⟩).lower ∧ (cell13008 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13008 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13008 ⟨35,by decide⟩).lower ∧ (cell13008 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13008 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13008 ⟨36,by decide⟩).lower ∧ (cell13008 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13008 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13008 ⟨37,by decide⟩).lower ∧ (cell13008 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13008 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13008 ⟨38,by decide⟩).lower ∧ (cell13008 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13008 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13008 ⟨39,by decide⟩).lower ∧ (cell13008 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13008 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13008 ⟨40,by decide⟩).lower ∧ (cell13008 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13008 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13008 ⟨41,by decide⟩).lower ∧ (cell13008 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13008 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13008 ⟨42,by decide⟩).lower ∧ (cell13008 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13008 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13008 ⟨43,by decide⟩).lower ∧ (cell13008 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13008 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13008 ⟨44,by decide⟩).lower ∧ (cell13008 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13008 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13008 ⟨45,by decide⟩).lower ∧ (cell13008 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13008 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13008 ⟨46,by decide⟩).lower ∧ (cell13008 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13008 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13008 ⟨47,by decide⟩).lower ∧ (cell13008 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13008 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13008 ⟨48,by decide⟩).lower ∧ (cell13008 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13008 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13008 ⟨49,by decide⟩).lower ∧ (cell13008 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13008 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13008 ⟨50,by decide⟩).lower ∧ (cell13008 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13008 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13008 ⟨51,by decide⟩).lower ∧ (cell13008 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13008 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13008 ⟨52,by decide⟩).lower ∧ (cell13008 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13008 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13008 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13008 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13008,cell13008,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13008 i).lower ∧
    (cell13008 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13008 i).upper ≤ (0.532 : ℝ) ∧
    (cell13008 i).centre ≤ (0.1 : ℝ) ∧ (cell13008 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13008 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13008 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13008

/-! The local source numeric instances at 13008 have no network premises. -/
namespace BstLean.Part269.N13008
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13008)
open BstLean.Part268 (cell13008)

noncomputable def sourceNumerics13008 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13008 (cell13008 i)
      scalarRow13008.M scalarRow13008.H scalarRow13008.xi := by
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
    energy_allowance := scalarRow13008.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13008]
    centre_nonneg := (scalarRow13008.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13008])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13008
/-! Actual 13009 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13009 ≤ (1.035377662632 : ℝ) := by
  have hr : (114.057003292213 : ℝ) ≤ √(13009 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.057003292213 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13009 13009 (11 / 1000) ≤
    (0.008380782541 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13009) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.057003292213 : ℝ) ≤ √(13009 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13009)
  have hdiv : K / √(13009 : ℝ) ≤ K / 114.057003292213 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.057003292213 ≤ (0.008380782541 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13009.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13009 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13009 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13009 := gPlus_lower 13009
end BstLean.Part269.N13009

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13009
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035377662631 : ℝ) ≤ wn 13009 := by
  have hn : √(13009 : ℝ) ≤ 114.057003292214 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13009 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.057003292214 ≤ 2 / √(13009 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245795546 : ℝ) ≤ rhoBar 13009 BstLean.Part154.csC ∧
    rhoBar 13009 BstLean.Part154.csC ≤ 0.000245795926 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035377662631 : ℝ) / (1.295212 * 13009) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035377662632 : ℝ) / (1.29521 * 13009) := by gcongr
      _ ≤ (0.000245795926 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13009 BstLean.Part154.csC) ≤ 0.000983244120 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13009 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) ≤ 0.000187740375 ∧
    cc1 (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) ≤ 0.000119460491 ∧
    cc2 (rhoBar 13009 BstLean.Part154.csC) ≤ 0.000069347783 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13009 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13009 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13009 BstLean.Part154.csC * nuR (rhoBar 13009 BstLean.Part154.csC)) ≤ 0.000491606956 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245795926 : ℝ) * 0.000983244120 := by gcongr
      _ ≤ (0.000491606956 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13009 BstLean.Part154.csC) * nuR (rhoBar 13009 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983244120 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13009 BstLean.Part154.csC) * rhoBar 13009 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245795926 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245795926 / 2 + 0.399 * 0.000983244120 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187740375 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491606956 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119460491 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245795926 / 1.414213562 := by gcongr
      _ ≤ (0.000069347783 : ℝ) := by norm_num

end BstLean.Part269.N13009

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13009
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) ≤ 1.52213E-7 := by
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13009 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13009 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13009 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187740375 : ℝ) ^ 2 + 0.000119460491 ^ 2 + 3 * 0.000069347783 ^ 2 +
        2 * 0.797885 * 0.000187740375 * 0.000119460491 + 2 * 0.000187740375 * 0.000069347783 +
        4 * 0.797885 * 0.000119460491 * 0.000069347783 := by gcongr
    _ ≤ (1.52213E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13009 BstLean.Part154.csC Θ ≤ 0.002564699691 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13009 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13009 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13009 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035377662632 * 1.52213E-7 / (0.000245795546 : ℝ) := by gcongr
    _ ≤ 0.002564699691 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13009 BstLean.Part154.csC Θ ≤ 0.002844480436 + 0.000648057702 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13009 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13009 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035377662632 : ℝ) * ((2 * Θ * 0.000245795926 +
        (6863 / 10000) * 0.000245795926 * 13009 * 0.000983244120) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002844480436 + 0.000648057702 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13009 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13009 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13009 0.011 Θ ∧ gammaRatio 13009 0.011 Θ ≤ 0.000084498284 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13009 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035377662632 : ℝ) * 0.525 / ((1 - 0.011) * 13009) := by gcongr
      _ ≤ (0.000084498284 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13009 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13009 0.011 Θ) :=
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
    badAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13009 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13009 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13009 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13009 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13009 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13009 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13009 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13009 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13009 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13009 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035377662632 : ℝ) * 13009 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003227190197 + 0.003212757393 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13009

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13009
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13009 BstLean.Part154.csC) (piBar (rhoBar 13009 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13009 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13009 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13009 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13009 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13009 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13009 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13009 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13009 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13009 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13009 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051850524039 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13009) ≤ 0.010470532687 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13009 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035377662632)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010470532687 + 2 * 0.737676 / 13009) := by gcongr
    _ ≤ (0.051850524039 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13009 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13009

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13009
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517210269 : ℝ) ≤ plow 13009 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13009) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420487829)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346467338) : eMP 13009 0.011 xi bn ≤ 0.001159587034 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13009 : ℝ) * (1 - 0.011))) ≤ 0.000573393505 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346467338 / (13009 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573393505 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573393505 : ℝ) + 3.141593 * 0.052420487829 / (13009 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159587034 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420487829)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346467338) : PiBarMP 13009 12 0.011 xi bn ≤ 0.159305253435 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13009 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036694241211 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.427955108077 : ℝ) ≤ √((13009 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.057003292213 : ℝ) ≤ √(13009 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13009) ≤ 0.122153027527 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036694241211 + 0.052420487829 * 1.772454 / (2 * (113.427955108077 : ℝ))) * (1 + 0.001159587034) +
        8 / (13009 * 114.057003292213) + 0.122153027527 := by gcongr
    _ ≤ (0.159305253435 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420487829)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346467338) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280805733260) :
    parallelOracle 13009 0.011 xi bn cd ≤ 0.160271810004 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13009 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13009 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517210269 : ℝ) ≤ plow 13009 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.057003292213 : ℝ) ≤ √(13009 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280805733260 : ℝ) / (2 * 0.560517210269 * 114.057003292213)) * 0.159305253435 +
        0.280805733260 ^ 2 / (2 * 0.560517210269 * 114.057003292213) := by gcongr
    _ ≤ (0.160271810004 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420487829) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346467338)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280805733260) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13009 13009 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517210269 : ℝ) ≤ plow 13009 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.057003292213 : ℝ) ≤ √(13009 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13009 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13009 Θ 1.22 ≤ 0.011626646868 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.057003292213 := by gcongr <;> linarith
      _ ≤ (0.011626646868 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13009 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13009 13009 0.011 ≤ 0.008380782541 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13009 13009 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13009 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13009 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13009 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13009 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160271810004 + 0.011626646868 + (0.008380782541 : ℝ) *
        (1 + 2 * (0.280805733260 + 0.011626646868) / (0.560517210269 * 114.057003292213))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13009]

end BstLean.Part269.N13009

/-! The original eight local profiles supply actual 13009 moment certificates. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13009 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052420487829 ∧
    0 ≤ bN 13009 BstLean.Part154.csC (groupTheta g) ∧ bN 13009 BstLean.Part154.csC (groupTheta g) ≤ 0.001346467338 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13009 13009 0.011
      (momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13009 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13009 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13009 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228955209221 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13009 0.011
      (momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13009 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13009
/-! The actual computed-centre upper energy formula at 13009. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13009

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13009)
open BstLean.Part268 (cell13009)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084636579928
  | 2 => 0.085564943347
  | 3 => 0.086489468736
  | 4 => 0.087411109420
  | 5 => 0.088331032136
  | 6 => 0.089250650425
  | 7 => 0.090171661483
  | 8 => 0.091096086579
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13009 13009 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13009 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13009

/-! Actual upper energy certificates on all 43 source endpoints at 13009. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13009)
open BstLean.Part268 (cell13009)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13009 (gMinus 13009) (1 - (cell13009 i).lower) ≤ 1 ∧
    energyUpper 13009 (gMinus 13009) (BstLean.Part211.gPlus 13009)
      (finiteEnergy 13009 13009 0.011) (1 - (cell13009 i).lower) ≤
      (cell13009 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨10,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨11,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨12,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨13,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨14,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨15,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨16,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨17,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨18,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨19,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨20,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨21,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨22,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨23,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨24,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨25,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨26,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨27,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨28,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨29,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨30,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨31,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨32,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨33,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨34,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨35,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨36,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨37,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨38,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨39,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨40,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨41,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨42,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨43,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨44,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨45,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨46,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨47,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨48,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨49,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨50,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨51,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13009) (by norm_num)
        (q := 1 - (cell13009 ⟨52,by decide⟩).lower)
        (by norm_num [cell13009]) (by norm_num [cell13009])
      exact ⟨E.1,E.2.trans (by norm_num [cell13009])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13009

/-! Source-cell containment and simple scalar guards at 13009. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13009)
open BstLean.Part268 (cell13009)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13009 ⟨10,by decide⟩).lower ∧ (cell13009 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13009 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13009 ⟨11,by decide⟩).lower ∧ (cell13009 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13009 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13009 ⟨12,by decide⟩).lower ∧ (cell13009 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13009 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13009 ⟨13,by decide⟩).lower ∧ (cell13009 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13009 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13009 ⟨14,by decide⟩).lower ∧ (cell13009 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13009 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13009 ⟨15,by decide⟩).lower ∧ (cell13009 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13009 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13009 ⟨16,by decide⟩).lower ∧ (cell13009 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13009 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13009 ⟨17,by decide⟩).lower ∧ (cell13009 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13009 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13009 ⟨18,by decide⟩).lower ∧ (cell13009 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13009 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13009 ⟨19,by decide⟩).lower ∧ (cell13009 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13009 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13009 ⟨20,by decide⟩).lower ∧ (cell13009 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13009 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13009 ⟨21,by decide⟩).lower ∧ (cell13009 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13009 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13009 ⟨22,by decide⟩).lower ∧ (cell13009 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13009 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13009 ⟨23,by decide⟩).lower ∧ (cell13009 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13009 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13009 ⟨24,by decide⟩).lower ∧ (cell13009 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13009 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13009 ⟨25,by decide⟩).lower ∧ (cell13009 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13009 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13009 ⟨26,by decide⟩).lower ∧ (cell13009 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13009 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13009 ⟨27,by decide⟩).lower ∧ (cell13009 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13009 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13009 ⟨28,by decide⟩).lower ∧ (cell13009 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13009 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13009 ⟨29,by decide⟩).lower ∧ (cell13009 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13009 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13009 ⟨30,by decide⟩).lower ∧ (cell13009 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13009 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13009 ⟨31,by decide⟩).lower ∧ (cell13009 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13009 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13009 ⟨32,by decide⟩).lower ∧ (cell13009 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13009 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13009 ⟨33,by decide⟩).lower ∧ (cell13009 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13009 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13009 ⟨34,by decide⟩).lower ∧ (cell13009 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13009 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13009 ⟨35,by decide⟩).lower ∧ (cell13009 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13009 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13009 ⟨36,by decide⟩).lower ∧ (cell13009 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13009 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13009 ⟨37,by decide⟩).lower ∧ (cell13009 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13009 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13009 ⟨38,by decide⟩).lower ∧ (cell13009 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13009 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13009 ⟨39,by decide⟩).lower ∧ (cell13009 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13009 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13009 ⟨40,by decide⟩).lower ∧ (cell13009 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13009 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13009 ⟨41,by decide⟩).lower ∧ (cell13009 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13009 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13009 ⟨42,by decide⟩).lower ∧ (cell13009 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13009 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13009 ⟨43,by decide⟩).lower ∧ (cell13009 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13009 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13009 ⟨44,by decide⟩).lower ∧ (cell13009 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13009 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13009 ⟨45,by decide⟩).lower ∧ (cell13009 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13009 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13009 ⟨46,by decide⟩).lower ∧ (cell13009 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13009 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13009 ⟨47,by decide⟩).lower ∧ (cell13009 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13009 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13009 ⟨48,by decide⟩).lower ∧ (cell13009 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13009 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13009 ⟨49,by decide⟩).lower ∧ (cell13009 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13009 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13009 ⟨50,by decide⟩).lower ∧ (cell13009 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13009 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13009 ⟨51,by decide⟩).lower ∧ (cell13009 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13009 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13009 ⟨52,by decide⟩).lower ∧ (cell13009 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13009 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13009 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13009 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13009,cell13009,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13009 i).lower ∧
    (cell13009 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13009 i).upper ≤ (0.532 : ℝ) ∧
    (cell13009 i).centre ≤ (0.1 : ℝ) ∧ (cell13009 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13009 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13009 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13009

/-! The local source numeric instances at 13009 have no network premises. -/
namespace BstLean.Part269.N13009
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13009)
open BstLean.Part268 (cell13009)

noncomputable def sourceNumerics13009 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13009 (cell13009 i)
      scalarRow13009.M scalarRow13009.H scalarRow13009.xi := by
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
    energy_allowance := scalarRow13009.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13009]
    centre_nonneg := (scalarRow13009.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13009])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13009
/-! Actual 13010 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13010 ≤ (1.035376291155 : ℝ) := by
  have hr : (114.061386980870 : ℝ) ≤ √(13010 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.061386980870 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13010 13010 (11 / 1000) ≤
    (0.008380460442 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13010) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.061386980870 : ℝ) ≤ √(13010 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13010)
  have hdiv : K / √(13010 : ℝ) ≤ K / 114.061386980870 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.061386980870 ≤ (0.008380460442 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13010.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13010 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13010 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13010 := gPlus_lower 13010
end BstLean.Part269.N13010

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13010
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035376291154 : ℝ) ≤ wn 13010 := by
  have hn : √(13010 : ℝ) ≤ 114.061386980871 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13010 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.061386980871 ≤ 2 / √(13010 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245776327 : ℝ) ≤ rhoBar 13010 BstLean.Part154.csC ∧
    rhoBar 13010 BstLean.Part154.csC ≤ 0.000245776708 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035376291154 : ℝ) / (1.295212 * 13010) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035376291155 : ℝ) / (1.29521 * 13010) := by gcongr
      _ ≤ (0.000245776708 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13010 BstLean.Part154.csC) ≤ 0.000983167239 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13010 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) ≤ 0.000187725696 ∧
    cc1 (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) ≤ 0.000119451150 ∧
    cc2 (rhoBar 13010 BstLean.Part154.csC) ≤ 0.000069342361 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13010 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13010 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13010 BstLean.Part154.csC * nuR (rhoBar 13010 BstLean.Part154.csC)) ≤ 0.000491568518 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245776708 : ℝ) * 0.000983167239 := by gcongr
      _ ≤ (0.000491568518 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13010 BstLean.Part154.csC) * nuR (rhoBar 13010 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983167239 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13010 BstLean.Part154.csC) * rhoBar 13010 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245776708 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245776708 / 2 + 0.399 * 0.000983167239 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187725696 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491568518 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119451150 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245776708 / 1.414213562 := by gcongr
      _ ≤ (0.000069342361 : ℝ) := by norm_num

end BstLean.Part269.N13010

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13010
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) ≤ 1.52189E-7 := by
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13010 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13010 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13010 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187725696 : ℝ) ^ 2 + 0.000119451150 ^ 2 + 3 * 0.000069342361 ^ 2 +
        2 * 0.797885 * 0.000187725696 * 0.000119451150 + 2 * 0.000187725696 * 0.000069342361 +
        4 * 0.797885 * 0.000119451150 * 0.000069342361 := by gcongr
    _ ≤ (1.52189E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13010 BstLean.Part154.csC Θ ≤ 0.002564492428 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13010 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13010 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13010 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035376291155 * 1.52189E-7 / (0.000245776327 : ℝ) := by gcongr
    _ ≤ 0.002564492428 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13010 BstLean.Part154.csC Θ ≤ 0.002844250492 + 0.000648006174 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13010 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13010 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035376291155 : ℝ) * ((2 * Θ * 0.000245776708 +
        (6863 / 10000) * 0.000245776708 * 13010 * 0.000983167239) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002844250492 + 0.000648006174 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13010 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13010 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13010 0.011 Θ ∧ gammaRatio 13010 0.011 Θ ≤ 0.000084491677 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13010 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035376291155 : ℝ) * 0.525 / ((1 - 0.011) * 13010) := by gcongr
      _ ≤ (0.000084491677 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13010 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13010 0.011 Θ) :=
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
    badAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13010 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13010 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13010 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13010 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13010 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13010 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13010 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13010 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13010 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13010 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035376291155 : ℝ) * 13010 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003226960253 + 0.003212498602 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13010

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13010
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13010 BstLean.Part154.csC) (piBar (rhoBar 13010 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13010 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13010 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13010 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13010 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13010 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13010 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13010 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13010 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13010 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13010 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051848509930 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13010) ≤ 0.010470130276 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13010 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035376291155)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010470130276 + 2 * 0.737676 / 13010) := by gcongr
    _ ≤ (0.051848509930 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13010 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13010

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13010
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517253366 : ℝ) ≤ plow 13010 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13010) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420122020)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346358525) : eMP 13010 0.011 xi bn ≤ 0.001159495551 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13010 : ℝ) * (1 - 0.011))) ≤ 0.000573348300 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346358525 / (13010 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573348300 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573348300 : ℝ) + 3.141593 * 0.052420122020 / (13010 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159495551 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420122020)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346358525) : PiBarMP 13010 12 0.011 xi bn ≤ 0.159299051678 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13010 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036692758482 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.432314619776 : ℝ) ≤ √((13010 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.061386980870 : ℝ) ≤ √(13010 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13010) ≤ 0.122148332855 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036692758482 + 0.052420122020 * 1.772454 / (2 * (113.432314619776 : ℝ))) * (1 + 0.001159495551) +
        8 / (13010 * 114.061386980870) + 0.122148332855 := by gcongr
    _ ≤ (0.159299051678 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420122020)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346358525) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280802920283) :
    parallelOracle 13010 0.011 xi bn cd ≤ 0.160265541546 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13010 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13010 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517253366 : ℝ) ≤ plow 13010 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.061386980870 : ℝ) ≤ √(13010 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280802920283 : ℝ) / (2 * 0.560517253366 * 114.061386980870)) * 0.159299051678 +
        0.280802920283 ^ 2 / (2 * 0.560517253366 * 114.061386980870) := by gcongr
    _ ≤ (0.160265541546 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052420122020) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346358525)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280802920283) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13010 13010 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517253366 : ℝ) ≤ plow 13010 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.061386980870 : ℝ) ≤ √(13010 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13010 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13010 Θ 1.22 ≤ 0.011626200024 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.061386980870 := by gcongr <;> linarith
      _ ≤ (0.011626200024 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13010 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13010 13010 0.011 ≤ 0.008380460442 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13010 13010 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13010 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13010 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13010 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13010 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160265541546 + 0.011626200024 + (0.008380460442 : ℝ) *
        (1 + 2 * (0.280802920283 + 0.011626200024) / (0.560517253366 * 114.061386980870))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13010]

end BstLean.Part269.N13010

/-! The original eight local profiles supply actual 13010 moment certificates. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13010 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052420122020 ∧
    0 ≤ bN 13010 BstLean.Part154.csC (groupTheta g) ∧ bN 13010 BstLean.Part154.csC (groupTheta g) ≤ 0.001346358525 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13010 13010 0.011
      (momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13010 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13010 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13010 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228954410353 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13010 0.011
      (momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13010 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13010
/-! The actual computed-centre upper energy formula at 13010. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13010

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13010)
open BstLean.Part268 (cell13010)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084633968952
  | 2 => 0.085562298078
  | 3 => 0.086486783980
  | 4 => 0.087408378764
  | 5 => 0.088328247728
  | 6 => 0.089247802721
  | 7 => 0.090168738964
  | 8 => 0.091093075435
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13010 13010 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13010 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13010

/-! Actual upper energy certificates on all 43 source endpoints at 13010. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13010)
open BstLean.Part268 (cell13010)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13010 (gMinus 13010) (1 - (cell13010 i).lower) ≤ 1 ∧
    energyUpper 13010 (gMinus 13010) (BstLean.Part211.gPlus 13010)
      (finiteEnergy 13010 13010 0.011) (1 - (cell13010 i).lower) ≤
      (cell13010 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨10,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨11,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨12,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨13,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨14,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨15,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨16,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨17,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨18,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨19,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨20,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨21,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨22,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨23,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨24,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨25,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨26,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨27,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨28,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨29,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨30,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨31,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨32,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨33,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨34,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨35,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨36,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨37,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨38,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨39,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨40,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨41,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨42,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨43,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨44,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨45,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨46,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨47,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨48,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨49,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨50,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨51,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13010) (by norm_num)
        (q := 1 - (cell13010 ⟨52,by decide⟩).lower)
        (by norm_num [cell13010]) (by norm_num [cell13010])
      exact ⟨E.1,E.2.trans (by norm_num [cell13010])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13010

/-! Source-cell containment and simple scalar guards at 13010. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13010)
open BstLean.Part268 (cell13010)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13010 ⟨10,by decide⟩).lower ∧ (cell13010 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13010 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13010 ⟨11,by decide⟩).lower ∧ (cell13010 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13010 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13010 ⟨12,by decide⟩).lower ∧ (cell13010 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13010 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13010 ⟨13,by decide⟩).lower ∧ (cell13010 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13010 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13010 ⟨14,by decide⟩).lower ∧ (cell13010 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13010 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13010 ⟨15,by decide⟩).lower ∧ (cell13010 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13010 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13010 ⟨16,by decide⟩).lower ∧ (cell13010 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13010 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13010 ⟨17,by decide⟩).lower ∧ (cell13010 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13010 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13010 ⟨18,by decide⟩).lower ∧ (cell13010 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13010 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13010 ⟨19,by decide⟩).lower ∧ (cell13010 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13010 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13010 ⟨20,by decide⟩).lower ∧ (cell13010 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13010 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13010 ⟨21,by decide⟩).lower ∧ (cell13010 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13010 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13010 ⟨22,by decide⟩).lower ∧ (cell13010 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13010 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13010 ⟨23,by decide⟩).lower ∧ (cell13010 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13010 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13010 ⟨24,by decide⟩).lower ∧ (cell13010 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13010 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13010 ⟨25,by decide⟩).lower ∧ (cell13010 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13010 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13010 ⟨26,by decide⟩).lower ∧ (cell13010 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13010 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13010 ⟨27,by decide⟩).lower ∧ (cell13010 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13010 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13010 ⟨28,by decide⟩).lower ∧ (cell13010 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13010 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13010 ⟨29,by decide⟩).lower ∧ (cell13010 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13010 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13010 ⟨30,by decide⟩).lower ∧ (cell13010 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13010 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13010 ⟨31,by decide⟩).lower ∧ (cell13010 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13010 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13010 ⟨32,by decide⟩).lower ∧ (cell13010 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13010 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13010 ⟨33,by decide⟩).lower ∧ (cell13010 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13010 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13010 ⟨34,by decide⟩).lower ∧ (cell13010 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13010 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13010 ⟨35,by decide⟩).lower ∧ (cell13010 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13010 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13010 ⟨36,by decide⟩).lower ∧ (cell13010 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13010 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13010 ⟨37,by decide⟩).lower ∧ (cell13010 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13010 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13010 ⟨38,by decide⟩).lower ∧ (cell13010 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13010 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13010 ⟨39,by decide⟩).lower ∧ (cell13010 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13010 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13010 ⟨40,by decide⟩).lower ∧ (cell13010 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13010 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13010 ⟨41,by decide⟩).lower ∧ (cell13010 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13010 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13010 ⟨42,by decide⟩).lower ∧ (cell13010 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13010 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13010 ⟨43,by decide⟩).lower ∧ (cell13010 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13010 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13010 ⟨44,by decide⟩).lower ∧ (cell13010 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13010 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13010 ⟨45,by decide⟩).lower ∧ (cell13010 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13010 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13010 ⟨46,by decide⟩).lower ∧ (cell13010 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13010 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13010 ⟨47,by decide⟩).lower ∧ (cell13010 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13010 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13010 ⟨48,by decide⟩).lower ∧ (cell13010 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13010 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13010 ⟨49,by decide⟩).lower ∧ (cell13010 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13010 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13010 ⟨50,by decide⟩).lower ∧ (cell13010 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13010 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13010 ⟨51,by decide⟩).lower ∧ (cell13010 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13010 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13010 ⟨52,by decide⟩).lower ∧ (cell13010 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13010 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13010 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13010 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13010,cell13010,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13010 i).lower ∧
    (cell13010 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13010 i).upper ≤ (0.532 : ℝ) ∧
    (cell13010 i).centre ≤ (0.1 : ℝ) ∧ (cell13010 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13010 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13010 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13010

/-! The local source numeric instances at 13010 have no network premises. -/
namespace BstLean.Part269.N13010
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13010)
open BstLean.Part268 (cell13010)

noncomputable def sourceNumerics13010 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13010 (cell13010 i)
      scalarRow13010.M scalarRow13010.H scalarRow13010.xi := by
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
    energy_allowance := scalarRow13010.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13010]
    centre_nonneg := (scalarRow13010.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13010])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13010
/-! Actual 13011 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13011 ≤ (1.035374919838 : ℝ) := by
  have hr : (114.065770501057 : ℝ) ≤ √(13011 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.065770501057 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13011 13011 (11 / 1000) ≤
    (0.008380138381 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13011) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.065770501057 : ℝ) ≤ √(13011 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13011)
  have hdiv : K / √(13011 : ℝ) ≤ K / 114.065770501057 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.065770501057 ≤ (0.008380138381 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13011.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13011 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13011 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13011 := gPlus_lower 13011
end BstLean.Part269.N13011

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13011
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035374919837 : ℝ) ≤ wn 13011 := by
  have hn : √(13011 : ℝ) ≤ 114.065770501058 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13011 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.065770501058 ≤ 2 / √(13011 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245757112 : ℝ) ≤ rhoBar 13011 BstLean.Part154.csC ∧
    rhoBar 13011 BstLean.Part154.csC ≤ 0.000245757493 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035374919837 : ℝ) / (1.295212 * 13011) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035374919838 : ℝ) / (1.29521 * 13011) := by gcongr
      _ ≤ (0.000245757493 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13011 BstLean.Part154.csC) ≤ 0.000983090369 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13011 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) ≤ 0.000187711019 ∧
    cc1 (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) ≤ 0.000119441811 ∧
    cc2 (rhoBar 13011 BstLean.Part154.csC) ≤ 0.000069336940 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13011 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13011 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13011 BstLean.Part154.csC * nuR (rhoBar 13011 BstLean.Part154.csC)) ≤ 0.000491530086 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245757493 : ℝ) * 0.000983090369 := by gcongr
      _ ≤ (0.000491530086 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13011 BstLean.Part154.csC) * nuR (rhoBar 13011 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983090369 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13011 BstLean.Part154.csC) * rhoBar 13011 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245757493 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245757493 / 2 + 0.399 * 0.000983090369 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187711019 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491530086 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119441811 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245757493 / 1.414213562 := by gcongr
      _ ≤ (0.000069336940 : ℝ) := by norm_num

end BstLean.Part269.N13011

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13011
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) ≤ 1.52165E-7 := by
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13011 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13011 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13011 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187711019 : ℝ) ^ 2 + 0.000119441811 ^ 2 + 3 * 0.000069336940 ^ 2 +
        2 * 0.797885 * 0.000187711019 * 0.000119441811 + 2 * 0.000187711019 * 0.000069336940 +
        4 * 0.797885 * 0.000119441811 * 0.000069336940 := by gcongr
    _ ≤ (1.52165E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13011 BstLean.Part154.csC Θ ≤ 0.002564285093 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13011 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13011 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13011 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035374919838 * 1.52165E-7 / (0.000245757112 : ℝ) := by gcongr
    _ ≤ 0.002564285093 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13011 BstLean.Part154.csC Θ ≤ 0.002844020583 + 0.000647954654 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13011 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13011 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035374919838 : ℝ) * ((2 * Θ * 0.000245757493 +
        (6863 / 10000) * 0.000245757493 * 13011 * 0.000983090369) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002844020583 + 0.000647954654 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13011 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13011 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13011 0.011 Θ ∧ gammaRatio 13011 0.011 Θ ≤ 0.000084485071 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13011 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035374919838 : ℝ) * 0.525 / ((1 - 0.011) * 13011) := by gcongr
      _ ≤ (0.000084485071 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13011 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13011 0.011 Θ) :=
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
    badAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13011 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13011 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13011 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13011 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13011 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13011 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13011 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13011 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13011 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13011 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035374919838 : ℝ) * 13011 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003226730344 + 0.003212239747 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13011

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13011
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13011 BstLean.Part154.csC) (piBar (rhoBar 13011 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13011 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13011 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13011 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13011 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13011 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13011 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13011 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13011 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13011 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13011 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051846496053 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13011) ≤ 0.010469727911 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13011 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035374919838)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010469727911 + 2 * 0.737676 / 13011) := by gcongr
    _ ≤ (0.051846496053 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13011 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13011

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13011
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517296456 : ℝ) ≤ plow 13011 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13011) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419756212)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346249674) : eMP 13011 0.011 xi bn ≤ 0.001159404056 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13011 : ℝ) * (1 - 0.011))) ≤ 0.000573303089 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346249674 / (13011 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573303089 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573303089 : ℝ) + 3.141593 * 0.052419756212 / (13011 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159404056 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419756212)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346249674) : PiBarMP 13011 12 0.011 xi bn ≤ 0.159292849887 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13011 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036691275176 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.436673963934 : ℝ) ≤ √((13011 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.065770501057 : ℝ) ≤ √(13011 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13011) ≤ 0.122143638724 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036691275176 + 0.052419756212 * 1.772454 / (2 * (113.436673963934 : ℝ))) * (1 + 0.001159404056) +
        8 / (13011 * 114.065770501057) + 0.122143638724 := by gcongr
    _ ≤ (0.159292849887 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419756212)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346249674) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280800107538) :
    parallelOracle 13011 0.011 xi bn cd ≤ 0.160259273063 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13011 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13011 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517296456 : ℝ) ≤ plow 13011 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.065770501057 : ℝ) ≤ √(13011 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280800107538 : ℝ) / (2 * 0.560517296456 * 114.065770501057)) * 0.159292849887 +
        0.280800107538 ^ 2 / (2 * 0.560517296456 * 114.065770501057) := by gcongr
    _ ≤ (0.160259273063 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419756212) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346249674)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280800107538) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13011 13011 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517296456 : ℝ) ≤ plow 13011 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.065770501057 : ℝ) ≤ √(13011 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13011 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13011 Θ 1.22 ≤ 0.011625753232 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.065770501057 := by gcongr <;> linarith
      _ ≤ (0.011625753232 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13011 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13011 13011 0.011 ≤ 0.008380138381 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13011 13011 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13011 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13011 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13011 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13011 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160259273063 + 0.011625753232 + (0.008380138381 : ℝ) *
        (1 + 2 * (0.280800107538 + 0.011625753232) / (0.560517296456 * 114.065770501057))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13011]

end BstLean.Part269.N13011

/-! The original eight local profiles supply actual 13011 moment certificates. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13011 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052419756212 ∧
    0 ≤ bN 13011 BstLean.Part154.csC (groupTheta g) ∧ bN 13011 BstLean.Part154.csC (groupTheta g) ≤ 0.001346249674 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13011 13011 0.011
      (momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13011 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13011 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13011 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228953611485 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13011 0.011
      (momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13011 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13011
/-! The actual computed-centre upper energy formula at 13011. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13011

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13011)
open BstLean.Part268 (cell13011)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084631358776
  | 2 => 0.085559653637
  | 3 => 0.086484100087
  | 4 => 0.087405649015
  | 5 => 0.088325464280
  | 6 => 0.089244956041
  | 7 => 0.090165817547
  | 8 => 0.091090065489
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13011 13011 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13011 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13011

/-! Actual upper energy certificates on all 43 source endpoints at 13011. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13011)
open BstLean.Part268 (cell13011)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13011 (gMinus 13011) (1 - (cell13011 i).lower) ≤ 1 ∧
    energyUpper 13011 (gMinus 13011) (BstLean.Part211.gPlus 13011)
      (finiteEnergy 13011 13011 0.011) (1 - (cell13011 i).lower) ≤
      (cell13011 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨10,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨11,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨12,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨13,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨14,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨15,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨16,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨17,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨18,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨19,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨20,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨21,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨22,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨23,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨24,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨25,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨26,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨27,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨28,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨29,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨30,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨31,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨32,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨33,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨34,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨35,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨36,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨37,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨38,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨39,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨40,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨41,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨42,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨43,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨44,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨45,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨46,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨47,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨48,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨49,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨50,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨51,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13011) (by norm_num)
        (q := 1 - (cell13011 ⟨52,by decide⟩).lower)
        (by norm_num [cell13011]) (by norm_num [cell13011])
      exact ⟨E.1,E.2.trans (by norm_num [cell13011])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13011

/-! Source-cell containment and simple scalar guards at 13011. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13011)
open BstLean.Part268 (cell13011)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13011 ⟨10,by decide⟩).lower ∧ (cell13011 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13011 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13011 ⟨11,by decide⟩).lower ∧ (cell13011 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13011 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13011 ⟨12,by decide⟩).lower ∧ (cell13011 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13011 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13011 ⟨13,by decide⟩).lower ∧ (cell13011 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13011 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13011 ⟨14,by decide⟩).lower ∧ (cell13011 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13011 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13011 ⟨15,by decide⟩).lower ∧ (cell13011 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13011 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13011 ⟨16,by decide⟩).lower ∧ (cell13011 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13011 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13011 ⟨17,by decide⟩).lower ∧ (cell13011 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13011 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13011 ⟨18,by decide⟩).lower ∧ (cell13011 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13011 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13011 ⟨19,by decide⟩).lower ∧ (cell13011 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13011 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13011 ⟨20,by decide⟩).lower ∧ (cell13011 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13011 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13011 ⟨21,by decide⟩).lower ∧ (cell13011 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13011 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13011 ⟨22,by decide⟩).lower ∧ (cell13011 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13011 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13011 ⟨23,by decide⟩).lower ∧ (cell13011 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13011 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13011 ⟨24,by decide⟩).lower ∧ (cell13011 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13011 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13011 ⟨25,by decide⟩).lower ∧ (cell13011 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13011 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13011 ⟨26,by decide⟩).lower ∧ (cell13011 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13011 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13011 ⟨27,by decide⟩).lower ∧ (cell13011 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13011 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13011 ⟨28,by decide⟩).lower ∧ (cell13011 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13011 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13011 ⟨29,by decide⟩).lower ∧ (cell13011 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13011 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13011 ⟨30,by decide⟩).lower ∧ (cell13011 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13011 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13011 ⟨31,by decide⟩).lower ∧ (cell13011 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13011 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13011 ⟨32,by decide⟩).lower ∧ (cell13011 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13011 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13011 ⟨33,by decide⟩).lower ∧ (cell13011 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13011 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13011 ⟨34,by decide⟩).lower ∧ (cell13011 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13011 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13011 ⟨35,by decide⟩).lower ∧ (cell13011 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13011 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13011 ⟨36,by decide⟩).lower ∧ (cell13011 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13011 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13011 ⟨37,by decide⟩).lower ∧ (cell13011 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13011 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13011 ⟨38,by decide⟩).lower ∧ (cell13011 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13011 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13011 ⟨39,by decide⟩).lower ∧ (cell13011 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13011 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13011 ⟨40,by decide⟩).lower ∧ (cell13011 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13011 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13011 ⟨41,by decide⟩).lower ∧ (cell13011 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13011 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13011 ⟨42,by decide⟩).lower ∧ (cell13011 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13011 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13011 ⟨43,by decide⟩).lower ∧ (cell13011 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13011 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13011 ⟨44,by decide⟩).lower ∧ (cell13011 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13011 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13011 ⟨45,by decide⟩).lower ∧ (cell13011 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13011 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13011 ⟨46,by decide⟩).lower ∧ (cell13011 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13011 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13011 ⟨47,by decide⟩).lower ∧ (cell13011 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13011 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13011 ⟨48,by decide⟩).lower ∧ (cell13011 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13011 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13011 ⟨49,by decide⟩).lower ∧ (cell13011 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13011 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13011 ⟨50,by decide⟩).lower ∧ (cell13011 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13011 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13011 ⟨51,by decide⟩).lower ∧ (cell13011 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13011 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13011 ⟨52,by decide⟩).lower ∧ (cell13011 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13011 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13011 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13011 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13011,cell13011,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13011 i).lower ∧
    (cell13011 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13011 i).upper ≤ (0.532 : ℝ) ∧
    (cell13011 i).centre ≤ (0.1 : ℝ) ∧ (cell13011 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13011 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13011 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13011

/-! The local source numeric instances at 13011 have no network premises. -/
namespace BstLean.Part269.N13011
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13011)
open BstLean.Part268 (cell13011)

noncomputable def sourceNumerics13011 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13011 (cell13011 i)
      scalarRow13011.M scalarRow13011.H scalarRow13011.xi := by
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
    energy_allowance := scalarRow13011.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13011]
    centre_nonneg := (scalarRow13011.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13011])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13011
/-! Actual 13012 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13012 ≤ (1.035373548680 : ℝ) := by
  have hr : (114.070153852793 : ℝ) ≤ √(13012 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.070153852793 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13012 13012 (11 / 1000) ≤
    (0.008379816356 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13012) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.070153852793 : ℝ) ≤ √(13012 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13012)
  have hdiv : K / √(13012 : ℝ) ≤ K / 114.070153852793 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.070153852793 ≤ (0.008379816356 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13012.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13012 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13012 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13012 := gPlus_lower 13012
end BstLean.Part269.N13012

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13012
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035373548679 : ℝ) ≤ wn 13012 := by
  have hn : √(13012 : ℝ) ≤ 114.070153852794 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13012 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.070153852794 ≤ 2 / √(13012 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000245737900 : ℝ) ≤ rhoBar 13012 BstLean.Part154.csC ∧
    rhoBar 13012 BstLean.Part154.csC ≤ 0.000245738280 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035373548679 : ℝ) / (1.295212 * 13012) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035373548680 : ℝ) / (1.29521 * 13012) := by gcongr
      _ ≤ (0.000245738280 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13012 BstLean.Part154.csC) ≤ 0.000983013508 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13012 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) ≤ 0.000187696343 ∧
    cc1 (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) ≤ 0.000119432473 ∧
    cc2 (rhoBar 13012 BstLean.Part154.csC) ≤ 0.000069331519 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13012 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13012 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13012 BstLean.Part154.csC * nuR (rhoBar 13012 BstLean.Part154.csC)) ≤ 0.000491491657 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000245738280 : ℝ) * 0.000983013508 := by gcongr
      _ ≤ (0.000491491657 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13012 BstLean.Part154.csC) * nuR (rhoBar 13012 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000983013508 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13012 BstLean.Part154.csC) * rhoBar 13012 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000245738280 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000245738280 / 2 + 0.399 * 0.000983013508 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000187696343 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000491491657 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119432473 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000245738280 / 1.414213562 := by gcongr
      _ ≤ (0.000069331519 : ℝ) := by norm_num

end BstLean.Part269.N13012

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13012
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) ≤ 1.52141E-7 := by
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13012 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13012 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13012 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000187696343 : ℝ) ^ 2 + 0.000119432473 ^ 2 + 3 * 0.000069331519 ^ 2 +
        2 * 0.797885 * 0.000187696343 * 0.000119432473 + 2 * 0.000187696343 * 0.000069331519 +
        4 * 0.797885 * 0.000119432473 * 0.000069331519 := by gcongr
    _ ≤ (1.52141E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13012 BstLean.Part154.csC Θ ≤ 0.002564077696 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13012 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13012 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13012 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035373548680 * 1.52141E-7 / (0.000245737900 : ℝ) := by gcongr
    _ ≤ 0.002564077696 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13012 BstLean.Part154.csC Θ ≤ 0.002843790690 + 0.000647903140 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13012 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13012 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035373548680 : ℝ) * ((2 * Θ * 0.000245738280 +
        (6863 / 10000) * 0.000245738280 * 13012 * 0.000983013508) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002843790690 + 0.000647903140 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13012 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13012 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13012 0.011 Θ ∧ gammaRatio 13012 0.011 Θ ≤ 0.000084478466 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13012 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035373548680 : ℝ) * 0.525 / ((1 - 0.011) * 13012) := by gcongr
      _ ≤ (0.000084478466 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13012 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13012 0.011 Θ) :=
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
    badAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000382709761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13012 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13012 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13012 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13012 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13012 0.011 Θ) 1.12 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 1 (gammaRatio 13012 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13012 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13012 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13012 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13012 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035373548680 : ℝ) * 13012 *
        (1.3781E-8 / 1.1045361 + 1.6832E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000382709761 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003226500451 + 0.003211980836 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13012

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13012
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13012 BstLean.Part154.csC) (piBar (rhoBar 13012 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13012 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13012 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13012 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13012 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13012 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13012 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13012 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13012 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13012 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13012 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051844482414 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13012) ≤ 0.010469325593 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13012 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035373548680)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010469325593 + 2 * 0.737676 / 13012) := by gcongr
    _ ≤ (0.051844482414 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13012 12 ≤ 0.0015 := by
  exact BstLean.Part269.S26.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13012

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13012
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560517339540 : ℝ) ≤ plow 13012 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13012) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419390390)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346140791) : eMP 13012 0.011 xi bn ≤ 0.001159312555 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13012 : ℝ) * (1 - 0.011))) ≤ 0.000573257875 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001346140791 / (13012 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000573257875 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000573257875 : ℝ) + 3.141593 * 0.052419390390 / (13012 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001159312555 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419390390)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346140791) : PiBarMP 13012 12 0.011 xi bn ≤ 0.159286648142 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13012 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036689791374 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.441033140570 : ℝ) ≤ √((13012 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.070153852793 : ℝ) ≤ √(13012 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13012) ≤ 0.122138945134 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036689791374 + 0.052419390390 * 1.772454 / (2 * (113.441033140570 : ℝ))) * (1 + 0.001159312555) +
        8 / (13012 * 114.070153852793) + 0.122138945134 := by gcongr
    _ ≤ (0.159286648142 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419390390)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346140791) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280797294998) :
    parallelOracle 13012 0.011 xi bn cd ≤ 0.160253004633 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13012 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13012 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560517339540 : ℝ) ≤ plow 13012 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.070153852793 : ℝ) ≤ √(13012 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280797294998 : ℝ) / (2 * 0.560517339540 * 114.070153852793)) * 0.159286648142 +
        0.280797294998 ^ 2 / (2 * 0.560517339540 * 114.070153852793) := by gcongr
    _ ≤ (0.160253004633 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052419390390) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001346140791)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280797294998) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13012 13012 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560517339540 : ℝ) ≤ plow 13012 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.070153852793 : ℝ) ≤ √(13012 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13012 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13012 Θ 1.22 ≤ 0.011625306491 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.070153852793 := by gcongr <;> linarith
      _ ≤ (0.011625306491 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13012 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13012 13012 0.011 ≤ 0.008379816356 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13012 13012 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13012 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13012 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13012 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13012 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160253004633 + 0.011625306491 + (0.008379816356 : ℝ) *
        (1 + 2 * (0.280797294998 + 0.011625306491) / (0.560517339540 * 114.070153852793))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13012]

end BstLean.Part269.N13012

/-! The original eight local profiles supply actual 13012 moment certificates. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13012 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052419390390 ∧
    0 ≤ bN 13012 BstLean.Part154.csC (groupTheta g) ∧ bN 13012 BstLean.Part154.csC (groupTheta g) ≤ 0.001346140791 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13012 13012 0.011
      (momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13012 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13012 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13012 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228952812584 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13012 0.011
      (momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13012 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13012
/-! The actual computed-centre upper energy formula at 13012. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13012

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13012)
open BstLean.Part268 (cell13012)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084628749399
  | 2 => 0.085557010025
  | 3 => 0.086481417057
  | 4 => 0.087402920172
  | 5 => 0.088322681790
  | 6 => 0.089242110384
  | 7 => 0.090162897232
  | 8 => 0.091087056739
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13012 13012 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13012 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003229261452 + 0.003215050469 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S26.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S26.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13012

/-! Actual upper energy certificates on all 43 source endpoints at 13012. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13012)
open BstLean.Part268 (cell13012)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13012 (gMinus 13012) (1 - (cell13012 i).lower) ≤ 1 ∧
    energyUpper 13012 (gMinus 13012) (BstLean.Part211.gPlus 13012)
      (finiteEnergy 13012 13012 0.011) (1 - (cell13012 i).lower) ≤
      (cell13012 i).energy := by
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
      have E := BstLean.Part269.S26.uniformEnergy10 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨10,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy11 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨11,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy12 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨12,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy13 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨13,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy14 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨14,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy15 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨15,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy16 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨16,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy17 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨17,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy18 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨18,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy19 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨19,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy20 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨20,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy21 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨21,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy22 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨22,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy23 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨23,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy24 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨24,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy25 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨25,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy26 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨26,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy27 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨27,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy28 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨28,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy29 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨29,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy30 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨30,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy31 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨31,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy32 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨32,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy33 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨33,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy34 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨34,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy35 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨35,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy36 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨36,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy37 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨37,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy38 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨38,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy39 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨39,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy40 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨40,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy41 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨41,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy42 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨42,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy43 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨43,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy44 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨44,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy45 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨45,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy46 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨46,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy47 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨47,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy48 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨48,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy49 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨49,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy50 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨50,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy51 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨51,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S26.uniformEnergy52 (n := 13012) (by norm_num)
        (q := 1 - (cell13012 ⟨52,by decide⟩).lower)
        (by norm_num [cell13012]) (by norm_num [cell13012])
      exact ⟨E.1,E.2.trans (by norm_num [cell13012])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13012

/-! Source-cell containment and simple scalar guards at 13012. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13012)
open BstLean.Part268 (cell13012)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13012 ⟨10,by decide⟩).lower ∧ (cell13012 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13012 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13012 ⟨11,by decide⟩).lower ∧ (cell13012 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13012 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13012 ⟨12,by decide⟩).lower ∧ (cell13012 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13012 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13012 ⟨13,by decide⟩).lower ∧ (cell13012 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13012 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13012 ⟨14,by decide⟩).lower ∧ (cell13012 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13012 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13012 ⟨15,by decide⟩).lower ∧ (cell13012 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13012 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13012 ⟨16,by decide⟩).lower ∧ (cell13012 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13012 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13012 ⟨17,by decide⟩).lower ∧ (cell13012 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13012 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13012 ⟨18,by decide⟩).lower ∧ (cell13012 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13012 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13012 ⟨19,by decide⟩).lower ∧ (cell13012 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13012 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13012 ⟨20,by decide⟩).lower ∧ (cell13012 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13012 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13012 ⟨21,by decide⟩).lower ∧ (cell13012 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13012 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13012 ⟨22,by decide⟩).lower ∧ (cell13012 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13012 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13012 ⟨23,by decide⟩).lower ∧ (cell13012 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13012 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13012 ⟨24,by decide⟩).lower ∧ (cell13012 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13012 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13012 ⟨25,by decide⟩).lower ∧ (cell13012 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13012 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13012 ⟨26,by decide⟩).lower ∧ (cell13012 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13012 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13012 ⟨27,by decide⟩).lower ∧ (cell13012 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13012 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13012 ⟨28,by decide⟩).lower ∧ (cell13012 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13012 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13012 ⟨29,by decide⟩).lower ∧ (cell13012 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13012 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13012 ⟨30,by decide⟩).lower ∧ (cell13012 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13012 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13012 ⟨31,by decide⟩).lower ∧ (cell13012 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13012 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13012 ⟨32,by decide⟩).lower ∧ (cell13012 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13012 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13012 ⟨33,by decide⟩).lower ∧ (cell13012 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13012 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13012 ⟨34,by decide⟩).lower ∧ (cell13012 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13012 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13012 ⟨35,by decide⟩).lower ∧ (cell13012 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13012 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13012 ⟨36,by decide⟩).lower ∧ (cell13012 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13012 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13012 ⟨37,by decide⟩).lower ∧ (cell13012 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13012 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13012 ⟨38,by decide⟩).lower ∧ (cell13012 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13012 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13012 ⟨39,by decide⟩).lower ∧ (cell13012 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13012 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13012 ⟨40,by decide⟩).lower ∧ (cell13012 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13012 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13012 ⟨41,by decide⟩).lower ∧ (cell13012 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13012 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13012 ⟨42,by decide⟩).lower ∧ (cell13012 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13012 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13012 ⟨43,by decide⟩).lower ∧ (cell13012 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13012 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13012 ⟨44,by decide⟩).lower ∧ (cell13012 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13012 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13012 ⟨45,by decide⟩).lower ∧ (cell13012 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13012 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13012 ⟨46,by decide⟩).lower ∧ (cell13012 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13012 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13012 ⟨47,by decide⟩).lower ∧ (cell13012 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13012 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13012 ⟨48,by decide⟩).lower ∧ (cell13012 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13012 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13012 ⟨49,by decide⟩).lower ∧ (cell13012 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13012 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13012 ⟨50,by decide⟩).lower ∧ (cell13012 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13012 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13012 ⟨51,by decide⟩).lower ∧ (cell13012 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13012 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13012 ⟨52,by decide⟩).lower ∧ (cell13012 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13012 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13012 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13012 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13012,cell13012,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13012 i).lower ∧
    (cell13012 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13012 i).upper ≤ (0.532 : ℝ) ∧
    (cell13012 i).centre ≤ (0.1 : ℝ) ∧ (cell13012 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13012 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13012 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13012

/-! The local source numeric instances at 13012 have no network premises. -/
namespace BstLean.Part269.N13012
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13012)
open BstLean.Part268 (cell13012)

noncomputable def sourceNumerics13012 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13012 (cell13012 i)
      scalarRow13012.M scalarRow13012.H scalarRow13012.xi := by
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
    energy_allowance := scalarRow13012.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13012]
    centre_nonneg := (scalarRow13012.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D26.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13012])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13012