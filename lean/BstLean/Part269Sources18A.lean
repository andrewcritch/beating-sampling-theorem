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
import BstLean.Part269Direction18
import BstLean.Part269Shared18
import BstLean.Part269Finite
import BstLean.Part269Rows18
import BstLean.Part269Source
/-! Actual 12800 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12800 ≤ (1.035667839060 : ℝ) := by
  have hr : (113.137084989847 : ℝ) ≤ √(12800 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.137084989847 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12800 12800 (11 / 1000) ≤
    (0.008448927250 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12800) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.137084989847 : ℝ) ≤ √(12800 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12800)
  have hdiv : K / √(12800 : ℝ) ≤ K / 113.137084989847 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.137084989847 ≤ (0.008448927250 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12800.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12800 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12800 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12800 := gPlus_lower 12800
end BstLean.Part269.N12800

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12800
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035667839059 : ℝ) ≤ wn 12800 := by
  have hn : √(12800 : ℝ) ≤ 113.137084989848 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12800 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.137084989848 ≤ 2 / √(12800 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249878938 : ℝ) ≤ rhoBar 12800 BstLean.Part154.csC ∧
    rhoBar 12800 BstLean.Part154.csC ≤ 0.000249879325 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035667839059 : ℝ) / (1.295212 * 12800) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035667839060 : ℝ) / (1.29521 * 12800) := by gcongr
      _ ≤ (0.000249879325 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12800 BstLean.Part154.csC) ≤ 0.000999579740 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12800 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) ≤ 0.000190859444 ∧
    cc1 (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) ≤ 0.000121445146 ∧
    cc2 (rhoBar 12800 BstLean.Part154.csC) ≤ 0.000070499855 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12800 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12800 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12800 BstLean.Part154.csC * nuR (rhoBar 12800 BstLean.Part154.csC)) ≤ 0.000499774260 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249879325 : ℝ) * 0.000999579740 := by gcongr
      _ ≤ (0.000499774260 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12800 BstLean.Part154.csC) * nuR (rhoBar 12800 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999579740 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12800 BstLean.Part154.csC) * rhoBar 12800 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249879325 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249879325 / 2 + 0.399 * 0.000999579740 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190859444 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499774260 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121445146 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249879325 / 1.414213562 := by gcongr
      _ ≤ (0.000070499855 : ℝ) := by norm_num

end BstLean.Part269.N12800

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12800
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) ≤ 1.57312E-7 := by
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12800 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12800 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12800 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190859444 : ℝ) ^ 2 + 0.000121445146 ^ 2 + 3 * 0.000070499855 ^ 2 +
        2 * 0.797885 * 0.000190859444 * 0.000121445146 + 2 * 0.000190859444 * 0.000070499855 +
        4 * 0.797885 * 0.000121445146 * 0.000070499855 := by gcongr
    _ ≤ (1.57312E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12800 BstLean.Part154.csC Θ ≤ 0.002608030600 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12800 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12800 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12800 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035667839060 * 1.57312E-7 / (0.000249878938 : ℝ) := by gcongr
    _ ≤ 0.002608030600 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12800 BstLean.Part154.csC Θ ≤ 0.002893359759 + 0.000659008505 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12800 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12800 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035667839060 : ℝ) * ((2 * Θ * 0.000249879325 +
        (6863 / 10000) * 0.000249879325 * 12800 * 0.000999579740) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002893359759 + 0.000659008505 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12800 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12800 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12800 0.011 Θ ∧ gammaRatio 12800 0.011 Θ ≤ 0.000085902050 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12800 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035667839060 : ℝ) * 0.525 / ((1 - 0.011) * 12800) := by gcongr
      _ ≤ (0.000085902050 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12800 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12800 0.011 Θ) :=
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
    badAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12800 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12800 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12800 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12800 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12800 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12800 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12800 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12800 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12800 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12800 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035667839060 : ℝ) * 12800 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003402164259 + 0.003267039105 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12800

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12800
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12800 BstLean.Part154.csC) (piBar (rhoBar 12800 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12800 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12800 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12800 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12800 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12800 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12800 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12800 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12800 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12800 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12800 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052276675219 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12800) ≤ 0.010555668649 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12800 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035667839060)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010555668649 + 2 * 0.737676 / 12800) := by gcongr
    _ ≤ (0.052276675219 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12800 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12800

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12800
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508055257 : ℝ) ≤ plow 12800 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12800) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623959790)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369216065) : eMP 12800 0.011 xi bn ≤ 0.001178896478 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12800 : ℝ) * (1 - 0.011))) ≤ 0.000582918479 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369216065 / (12800 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582918479 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582918479 : ℝ) + 3.141593 * 0.052623959790 / (12800 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178896478 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623959790)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369216065) : PiBarMP 12800 12 0.011 xi bn ≤ 0.160613310529 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12800 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037002919683 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.513110347194 : ℝ) ≤ √((12800 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.137084989847 : ℝ) ≤ √(12800 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12800) ≤ 0.123146254511 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037002919683 + 0.052623959790 * 1.772454 / (2 * (112.513110347194 : ℝ))) * (1 + 0.001178896478) +
        8 / (12800 * 113.137084989847) + 0.123146254511 := by gcongr
    _ ≤ (0.160613310529 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623959790)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369216065) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281675802921) :
    parallelOracle 12800 0.011 xi bn cd ≤ 0.161595598786 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12800 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12800 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508055257 : ℝ) ≤ plow 12800 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.137084989847 : ℝ) ≤ √(12800 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281675802921 : ℝ) / (2 * 0.560508055257 * 113.137084989847)) * 0.160613310529 +
        0.281675802921 ^ 2 / (2 * 0.560508055257 * 113.137084989847) := by gcongr
    _ ≤ (0.161595598786 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623959790) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369216065)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281675802921) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12800 12800 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508055257 : ℝ) ≤ plow 12800 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.137084989847 : ℝ) ≤ √(12800 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12800 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12800 Θ 1.22 ≤ 0.011721183202 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.137084989847 := by gcongr <;> linarith
      _ ≤ (0.011721183202 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12800 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12800 12800 0.011 ≤ 0.008448927250 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12800 12800 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12800 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12800 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12800 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12800 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161595598786 + 0.011721183202 + (0.008448927250 : ℝ) *
        (1 + 2 * (0.281675802921 + 0.011721183202) / (0.560508055257 * 113.137084989847))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12800]

end BstLean.Part269.N12800

/-! The original eight local profiles supply actual 12800 moment certificates. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12800 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052623959790 ∧
    0 ≤ bN 12800 BstLean.Part154.csC (groupTheta g) ∧ bN 12800 BstLean.Part154.csC (groupTheta g) ≤ 0.001369216065 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12800 12800 0.011
      (momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12800 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12800 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12800 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229399127702 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12800 0.011
      (momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12800 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12800
/-! The actual computed-centre upper energy formula at 12800. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12800

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12800)
open BstLean.Part268 (cell12800)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085203869232
  | 2 => 0.086141473787
  | 3 => 0.087076486470
  | 4 => 0.088010155516
  | 5 => 0.088943996118
  | 6 => 0.089879830767
  | 7 => 0.090819833518
  | 8 => 0.091766578239
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12800 12800 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12800 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12800

/-! Actual upper energy certificates on all 43 source endpoints at 12800. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12800)
open BstLean.Part268 (cell12800)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12800 (gMinus 12800) (1 - (cell12800 i).lower) ≤ 1 ∧
    energyUpper 12800 (gMinus 12800) (BstLean.Part211.gPlus 12800)
      (finiteEnergy 12800 12800 0.011) (1 - (cell12800 i).lower) ≤
      (cell12800 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨10,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨11,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨12,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨13,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨14,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨15,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨16,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨17,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨18,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨19,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨20,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨21,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨22,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨23,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨24,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨25,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨26,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨27,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨28,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨29,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨30,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨31,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨32,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨33,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨34,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨35,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨36,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨37,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨38,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨39,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨40,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨41,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨42,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨43,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨44,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨45,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨46,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨47,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨48,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨49,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨50,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨51,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12800) (by norm_num)
        (q := 1 - (cell12800 ⟨52,by decide⟩).lower)
        (by norm_num [cell12800]) (by norm_num [cell12800])
      exact ⟨E.1,E.2.trans (by norm_num [cell12800])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12800

/-! Source-cell containment and simple scalar guards at 12800. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12800)
open BstLean.Part268 (cell12800)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12800 ⟨10,by decide⟩).lower ∧ (cell12800 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12800 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12800 ⟨11,by decide⟩).lower ∧ (cell12800 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12800 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12800 ⟨12,by decide⟩).lower ∧ (cell12800 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12800 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12800 ⟨13,by decide⟩).lower ∧ (cell12800 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12800 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12800 ⟨14,by decide⟩).lower ∧ (cell12800 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12800 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12800 ⟨15,by decide⟩).lower ∧ (cell12800 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12800 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12800 ⟨16,by decide⟩).lower ∧ (cell12800 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12800 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12800 ⟨17,by decide⟩).lower ∧ (cell12800 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12800 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12800 ⟨18,by decide⟩).lower ∧ (cell12800 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12800 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12800 ⟨19,by decide⟩).lower ∧ (cell12800 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12800 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12800 ⟨20,by decide⟩).lower ∧ (cell12800 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12800 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12800 ⟨21,by decide⟩).lower ∧ (cell12800 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12800 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12800 ⟨22,by decide⟩).lower ∧ (cell12800 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12800 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12800 ⟨23,by decide⟩).lower ∧ (cell12800 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12800 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12800 ⟨24,by decide⟩).lower ∧ (cell12800 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12800 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12800 ⟨25,by decide⟩).lower ∧ (cell12800 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12800 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12800 ⟨26,by decide⟩).lower ∧ (cell12800 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12800 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12800 ⟨27,by decide⟩).lower ∧ (cell12800 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12800 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12800 ⟨28,by decide⟩).lower ∧ (cell12800 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12800 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12800 ⟨29,by decide⟩).lower ∧ (cell12800 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12800 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12800 ⟨30,by decide⟩).lower ∧ (cell12800 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12800 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12800 ⟨31,by decide⟩).lower ∧ (cell12800 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12800 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12800 ⟨32,by decide⟩).lower ∧ (cell12800 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12800 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12800 ⟨33,by decide⟩).lower ∧ (cell12800 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12800 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12800 ⟨34,by decide⟩).lower ∧ (cell12800 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12800 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12800 ⟨35,by decide⟩).lower ∧ (cell12800 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12800 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12800 ⟨36,by decide⟩).lower ∧ (cell12800 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12800 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12800 ⟨37,by decide⟩).lower ∧ (cell12800 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12800 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12800 ⟨38,by decide⟩).lower ∧ (cell12800 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12800 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12800 ⟨39,by decide⟩).lower ∧ (cell12800 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12800 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12800 ⟨40,by decide⟩).lower ∧ (cell12800 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12800 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12800 ⟨41,by decide⟩).lower ∧ (cell12800 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12800 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12800 ⟨42,by decide⟩).lower ∧ (cell12800 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12800 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12800 ⟨43,by decide⟩).lower ∧ (cell12800 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12800 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12800 ⟨44,by decide⟩).lower ∧ (cell12800 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12800 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12800 ⟨45,by decide⟩).lower ∧ (cell12800 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12800 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12800 ⟨46,by decide⟩).lower ∧ (cell12800 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12800 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12800 ⟨47,by decide⟩).lower ∧ (cell12800 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12800 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12800 ⟨48,by decide⟩).lower ∧ (cell12800 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12800 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12800 ⟨49,by decide⟩).lower ∧ (cell12800 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12800 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12800 ⟨50,by decide⟩).lower ∧ (cell12800 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12800 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12800 ⟨51,by decide⟩).lower ∧ (cell12800 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12800 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12800 ⟨52,by decide⟩).lower ∧ (cell12800 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12800 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12800 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12800 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12800,cell12800,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12800 i).lower ∧
    (cell12800 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12800 i).upper ≤ (0.532 : ℝ) ∧
    (cell12800 i).centre ≤ (0.1 : ℝ) ∧ (cell12800 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12800 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12800 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12800

/-! The local source numeric instances at 12800 have no network premises. -/
namespace BstLean.Part269.N12800
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12800)
open BstLean.Part268 (cell12800)

noncomputable def sourceNumerics12800 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12800 (cell12800 i)
      scalarRow12800.M scalarRow12800.H scalarRow12800.xi := by
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
    energy_allowance := scalarRow12800.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12800]
    centre_nonneg := (scalarRow12800.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12800])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12800
/-! Actual 12801 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12801 ≤ (1.035666433661 : ℝ) := by
  have hr : (113.141504320916 : ℝ) ≤ √(12801 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.141504320916 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12801 12801 (11 / 1000) ≤
    (0.008448597231 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12801) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.141504320916 : ℝ) ≤ √(12801 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12801)
  have hdiv : K / √(12801 : ℝ) ≤ K / 113.141504320916 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.141504320916 ≤ (0.008448597231 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12801.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12801 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12801 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12801 := gPlus_lower 12801
end BstLean.Part269.N12801

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12801
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035666433660 : ℝ) ≤ wn 12801 := by
  have hn : √(12801 : ℝ) ≤ 113.141504320917 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12801 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.141504320917 ≤ 2 / √(12801 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249859079 : ℝ) ≤ rhoBar 12801 BstLean.Part154.csC ∧
    rhoBar 12801 BstLean.Part154.csC ≤ 0.000249859466 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035666433660 : ℝ) / (1.295212 * 12801) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035666433661 : ℝ) / (1.29521 * 12801) := by gcongr
      _ ≤ (0.000249859466 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12801 BstLean.Part154.csC) ≤ 0.000999500294 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12801 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) ≤ 0.000190844274 ∧
    cc1 (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) ≤ 0.000121435494 ∧
    cc2 (rhoBar 12801 BstLean.Part154.csC) ≤ 0.000070494252 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12801 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12801 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12801 BstLean.Part154.csC * nuR (rhoBar 12801 BstLean.Part154.csC)) ≤ 0.000499734540 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249859466 : ℝ) * 0.000999500294 := by gcongr
      _ ≤ (0.000499734540 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12801 BstLean.Part154.csC) * nuR (rhoBar 12801 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999500294 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12801 BstLean.Part154.csC) * rhoBar 12801 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249859466 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249859466 / 2 + 0.399 * 0.000999500294 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190844274 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499734540 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121435494 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249859466 / 1.414213562 := by gcongr
      _ ≤ (0.000070494252 : ℝ) := by norm_num

end BstLean.Part269.N12801

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12801
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) ≤ 1.57287E-7 := by
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12801 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12801 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12801 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190844274 : ℝ) ^ 2 + 0.000121435494 ^ 2 + 3 * 0.000070494252 ^ 2 +
        2 * 0.797885 * 0.000190844274 * 0.000121435494 + 2 * 0.000190844274 * 0.000070494252 +
        4 * 0.797885 * 0.000121435494 * 0.000070494252 := by gcongr
    _ ≤ (1.57287E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12801 BstLean.Part154.csC Θ ≤ 0.002607819848 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12801 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12801 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12801 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035666433661 * 1.57287E-7 / (0.000249859079 : ℝ) := by gcongr
    _ ≤ 0.002607819848 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12801 BstLean.Part154.csC Θ ≤ 0.002893121948 + 0.000658955236 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12801 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12801 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035666433661 : ℝ) * ((2 * Θ * 0.000249859466 +
        (6863 / 10000) * 0.000249859466 * 12801 * 0.000999500294) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002893121948 + 0.000658955236 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12801 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12801 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12801 0.011 Θ ∧ gammaRatio 12801 0.011 Θ ≤ 0.000085895223 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12801 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035666433661 : ℝ) * 0.525 / ((1 - 0.011) * 12801) := by gcongr
      _ ≤ (0.000085895223 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12801 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12801 0.011 Θ) :=
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
    badAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12801 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12801 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12801 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12801 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12801 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12801 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12801 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12801 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12801 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12801 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035666433661 : ℝ) * 12801 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003401926448 + 0.003266775084 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12801

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12801
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12801 BstLean.Part154.csC) (piBar (rhoBar 12801 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12801 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12801 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12801 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12801 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12801 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12801 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12801 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12801 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12801 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12801 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052274611229 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12801) ≤ 0.010555256343 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12801 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035666433661)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010555256343 + 2 * 0.737676 / 12801) := by gcongr
    _ ≤ (0.052274611229 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12801 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12801

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12801
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508099773 : ℝ) ≤ plow 12801 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12801) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623583368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369105421) : eMP 12801 0.011 xi bn ≤ 0.001178802722 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12801 : ℝ) * (1 - 0.011))) ≤ 0.000582872158 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001369105421 / (12801 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582872158 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582872158 : ℝ) + 3.141593 * 0.052623583368 / (12801 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178802722 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623583368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369105421) : PiBarMP 12801 12 0.011 xi bn ≤ 0.160606980213 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12801 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037001424581 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.517505304730 : ℝ) ≤ √((12801 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.141504320916 : ℝ) ≤ √(12801 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12801) ≤ 0.123141444392 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037001424581 + 0.052623583368 * 1.772454 / (2 * (112.517505304730 : ℝ))) * (1 + 0.001178802722) +
        8 / (12801 * 113.141504320916) + 0.123141444392 := by gcongr
    _ ≤ (0.160606980213 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623583368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369105421) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281672918477) :
    parallelOracle 12801 0.011 xi bn cd ≤ 0.161589199500 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12801 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12801 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508099773 : ℝ) ≤ plow 12801 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.141504320916 : ℝ) ≤ √(12801 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281672918477 : ℝ) / (2 * 0.560508099773 * 113.141504320916)) * 0.160606980213 +
        0.281672918477 ^ 2 / (2 * 0.560508099773 * 113.141504320916) := by gcongr
    _ ≤ (0.161589199500 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623583368) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001369105421)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281672918477) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12801 12801 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508099773 : ℝ) ≤ plow 12801 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.141504320916 : ℝ) ≤ √(12801 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12801 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12801 Θ 1.22 ≤ 0.011720725370 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.141504320916 := by gcongr <;> linarith
      _ ≤ (0.011720725370 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12801 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12801 12801 0.011 ≤ 0.008448597231 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12801 12801 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12801 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12801 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12801 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12801 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161589199500 + 0.011720725370 + (0.008448597231 : ℝ) *
        (1 + 2 * (0.281672918477 + 0.011720725370) / (0.560508099773 * 113.141504320916))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12801]

end BstLean.Part269.N12801

/-! The original eight local profiles supply actual 12801 moment certificates. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12801 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052623583368 ∧
    0 ≤ bN 12801 BstLean.Part154.csC (groupTheta g) ∧ bN 12801 BstLean.Part154.csC (groupTheta g) ≤ 0.001369105421 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12801 12801 0.011
      (momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12801 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12801 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12801 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229398307248 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12801 0.011
      (momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12801 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12801
/-! The actual computed-centre upper energy formula at 12801. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12801

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12801)
open BstLean.Part268 (cell12801)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085201056560
  | 2 => 0.086138611730
  | 3 => 0.087073568197
  | 4 => 0.088007172597
  | 5 => 0.088940938240
  | 6 => 0.089876685406
  | 7 => 0.090816585582
  | 8 => 0.091763209661
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12801 12801 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12801 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12801

/-! Actual upper energy certificates on all 43 source endpoints at 12801. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12801)
open BstLean.Part268 (cell12801)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12801 (gMinus 12801) (1 - (cell12801 i).lower) ≤ 1 ∧
    energyUpper 12801 (gMinus 12801) (BstLean.Part211.gPlus 12801)
      (finiteEnergy 12801 12801 0.011) (1 - (cell12801 i).lower) ≤
      (cell12801 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨10,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨11,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨12,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨13,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨14,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨15,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨16,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨17,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨18,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨19,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨20,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨21,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨22,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨23,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨24,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨25,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨26,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨27,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨28,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨29,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨30,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨31,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨32,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨33,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨34,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨35,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨36,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨37,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨38,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨39,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨40,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨41,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨42,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨43,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨44,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨45,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨46,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨47,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨48,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨49,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨50,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨51,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12801) (by norm_num)
        (q := 1 - (cell12801 ⟨52,by decide⟩).lower)
        (by norm_num [cell12801]) (by norm_num [cell12801])
      exact ⟨E.1,E.2.trans (by norm_num [cell12801])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12801

/-! Source-cell containment and simple scalar guards at 12801. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12801)
open BstLean.Part268 (cell12801)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12801 ⟨10,by decide⟩).lower ∧ (cell12801 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12801 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12801 ⟨11,by decide⟩).lower ∧ (cell12801 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12801 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12801 ⟨12,by decide⟩).lower ∧ (cell12801 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12801 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12801 ⟨13,by decide⟩).lower ∧ (cell12801 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12801 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12801 ⟨14,by decide⟩).lower ∧ (cell12801 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12801 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12801 ⟨15,by decide⟩).lower ∧ (cell12801 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12801 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12801 ⟨16,by decide⟩).lower ∧ (cell12801 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12801 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12801 ⟨17,by decide⟩).lower ∧ (cell12801 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12801 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12801 ⟨18,by decide⟩).lower ∧ (cell12801 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12801 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12801 ⟨19,by decide⟩).lower ∧ (cell12801 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12801 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12801 ⟨20,by decide⟩).lower ∧ (cell12801 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12801 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12801 ⟨21,by decide⟩).lower ∧ (cell12801 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12801 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12801 ⟨22,by decide⟩).lower ∧ (cell12801 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12801 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12801 ⟨23,by decide⟩).lower ∧ (cell12801 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12801 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12801 ⟨24,by decide⟩).lower ∧ (cell12801 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12801 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12801 ⟨25,by decide⟩).lower ∧ (cell12801 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12801 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12801 ⟨26,by decide⟩).lower ∧ (cell12801 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12801 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12801 ⟨27,by decide⟩).lower ∧ (cell12801 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12801 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12801 ⟨28,by decide⟩).lower ∧ (cell12801 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12801 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12801 ⟨29,by decide⟩).lower ∧ (cell12801 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12801 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12801 ⟨30,by decide⟩).lower ∧ (cell12801 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12801 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12801 ⟨31,by decide⟩).lower ∧ (cell12801 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12801 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12801 ⟨32,by decide⟩).lower ∧ (cell12801 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12801 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12801 ⟨33,by decide⟩).lower ∧ (cell12801 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12801 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12801 ⟨34,by decide⟩).lower ∧ (cell12801 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12801 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12801 ⟨35,by decide⟩).lower ∧ (cell12801 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12801 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12801 ⟨36,by decide⟩).lower ∧ (cell12801 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12801 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12801 ⟨37,by decide⟩).lower ∧ (cell12801 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12801 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12801 ⟨38,by decide⟩).lower ∧ (cell12801 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12801 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12801 ⟨39,by decide⟩).lower ∧ (cell12801 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12801 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12801 ⟨40,by decide⟩).lower ∧ (cell12801 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12801 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12801 ⟨41,by decide⟩).lower ∧ (cell12801 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12801 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12801 ⟨42,by decide⟩).lower ∧ (cell12801 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12801 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12801 ⟨43,by decide⟩).lower ∧ (cell12801 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12801 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12801 ⟨44,by decide⟩).lower ∧ (cell12801 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12801 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12801 ⟨45,by decide⟩).lower ∧ (cell12801 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12801 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12801 ⟨46,by decide⟩).lower ∧ (cell12801 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12801 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12801 ⟨47,by decide⟩).lower ∧ (cell12801 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12801 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12801 ⟨48,by decide⟩).lower ∧ (cell12801 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12801 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12801 ⟨49,by decide⟩).lower ∧ (cell12801 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12801 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12801 ⟨50,by decide⟩).lower ∧ (cell12801 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12801 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12801 ⟨51,by decide⟩).lower ∧ (cell12801 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12801 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12801 ⟨52,by decide⟩).lower ∧ (cell12801 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12801 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12801 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12801 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12801,cell12801,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12801 i).lower ∧
    (cell12801 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12801 i).upper ≤ (0.532 : ℝ) ∧
    (cell12801 i).centre ≤ (0.1 : ℝ) ∧ (cell12801 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12801 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12801 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12801

/-! The local source numeric instances at 12801 have no network premises. -/
namespace BstLean.Part269.N12801
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12801)
open BstLean.Part268 (cell12801)

noncomputable def sourceNumerics12801 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12801 (cell12801 i)
      scalarRow12801.M scalarRow12801.H scalarRow12801.xi := by
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
    energy_allowance := scalarRow12801.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12801]
    centre_nonneg := (scalarRow12801.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12801])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12801
/-! Actual 12802 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12802 ≤ (1.035665028427 : ℝ) := by
  have hr : (113.145923479372 : ℝ) ≤ √(12802 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.145923479372 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12802 12802 (11 / 1000) ≤
    (0.008448267250 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12802) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.145923479372 : ℝ) ≤ √(12802 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12802)
  have hdiv : K / √(12802 : ℝ) ≤ K / 113.145923479372 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.145923479372 ≤ (0.008448267250 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12802.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12802 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12802 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12802 := gPlus_lower 12802
end BstLean.Part269.N12802

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12802
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035665028426 : ℝ) ≤ wn 12802 := by
  have hn : √(12802 : ℝ) ≤ 113.145923479373 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12802 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.145923479373 ≤ 2 / √(12802 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249839223 : ℝ) ≤ rhoBar 12802 BstLean.Part154.csC ∧
    rhoBar 12802 BstLean.Part154.csC ≤ 0.000249839609 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035665028426 : ℝ) / (1.295212 * 12802) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035665028427 : ℝ) / (1.29521 * 12802) := by gcongr
      _ ≤ (0.000249839609 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12802 BstLean.Part154.csC) ≤ 0.000999420856 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12802 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) ≤ 0.000190829107 ∧
    cc1 (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) ≤ 0.000121425842 ∧
    cc2 (rhoBar 12802 BstLean.Part154.csC) ≤ 0.000070488650 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12802 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12802 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12802 BstLean.Part154.csC * nuR (rhoBar 12802 BstLean.Part154.csC)) ≤ 0.000499694823 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249839609 : ℝ) * 0.000999420856 := by gcongr
      _ ≤ (0.000499694823 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12802 BstLean.Part154.csC) * nuR (rhoBar 12802 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999420856 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12802 BstLean.Part154.csC) * rhoBar 12802 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249839609 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249839609 / 2 + 0.399 * 0.000999420856 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190829107 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499694823 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121425842 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249839609 / 1.414213562 := by gcongr
      _ ≤ (0.000070488650 : ℝ) := by norm_num

end BstLean.Part269.N12802

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12802
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) ≤ 1.57262E-7 := by
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12802 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12802 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12802 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190829107 : ℝ) ^ 2 + 0.000121425842 ^ 2 + 3 * 0.000070488650 ^ 2 +
        2 * 0.797885 * 0.000190829107 * 0.000121425842 + 2 * 0.000190829107 * 0.000070488650 +
        4 * 0.797885 * 0.000121425842 * 0.000070488650 := by gcongr
    _ ≤ (1.57262E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12802 BstLean.Part154.csC Θ ≤ 0.002607609034 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12802 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12802 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12802 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035665028427 * 1.57262E-7 / (0.000249839223 : ℝ) := by gcongr
    _ ≤ 0.002607609034 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12802 BstLean.Part154.csC Θ ≤ 0.002892884150 + 0.000658901973 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12802 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12802 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035665028427 : ℝ) * ((2 * Θ * 0.000249839609 +
        (6863 / 10000) * 0.000249839609 * 12802 * 0.000999420856) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002892884150 + 0.000658901973 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12802 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12802 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12802 0.011 Θ ∧ gammaRatio 12802 0.011 Θ ≤ 0.000085888397 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12802 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035665028427 : ℝ) * 0.525 / ((1 - 0.011) * 12802) := by gcongr
      _ ≤ (0.000085888397 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12802 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12802 0.011 Θ) :=
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
    badAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12802 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12802 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12802 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12802 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12802 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12802 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12802 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12802 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12802 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12802 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035665028427 : ℝ) * 12802 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003401688650 + 0.003266511007 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12802

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12802
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12802 BstLean.Part154.csC) (piBar (rhoBar 12802 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12802 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12802 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12802 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12802 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12802 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12802 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12802 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12802 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12802 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12802 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052272547476 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12802) ≤ 0.010554844084 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12802 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035665028427)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010554844084 + 2 * 0.737676 / 12802) := by gcongr
    _ ≤ (0.052272547476 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12802 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12802

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12802
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508144282 : ℝ) ≤ plow 12802 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12802) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623206929)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368994743) : eMP 12802 0.011 xi bn ≤ 0.001178708961 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12802 : ℝ) * (1 - 0.011))) ≤ 0.000582825834 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368994743 / (12802 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582825834 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582825834 : ℝ) + 3.141593 * 0.052623206929 / (12802 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178708961 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623206929)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368994743) : PiBarMP 12802 12 0.011 xi bn ≤ 0.160600649942 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12802 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036999928960 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.521900090604 : ℝ) ≤ √((12802 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.145923479372 : ℝ) ≤ √(12802 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12802) ≤ 0.123136634837 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036999928960 + 0.052623206929 * 1.772454 / (2 * (112.521900090604 : ℝ))) * (1 + 0.001178708961) +
        8 / (12802 * 113.145923479372) + 0.123136634837 := by gcongr
    _ ≤ (0.160600649942 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623206929)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368994743) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281670034230) :
    parallelOracle 12802 0.011 xi bn cd ≤ 0.161582800269 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12802 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12802 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508144282 : ℝ) ≤ plow 12802 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.145923479372 : ℝ) ≤ √(12802 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281670034230 : ℝ) / (2 * 0.560508144282 * 113.145923479372)) * 0.160600649942 +
        0.281670034230 ^ 2 / (2 * 0.560508144282 * 113.145923479372) := by gcongr
    _ ≤ (0.161582800269 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052623206929) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368994743)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281670034230) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12802 12802 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508144282 : ℝ) ≤ plow 12802 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.145923479372 : ℝ) ≤ √(12802 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12802 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12802 Θ 1.22 ≤ 0.011720267591 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.145923479372 := by gcongr <;> linarith
      _ ≤ (0.011720267591 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12802 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12802 12802 0.011 ≤ 0.008448267250 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12802 12802 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12802 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12802 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12802 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12802 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161582800269 + 0.011720267591 + (0.008448267250 : ℝ) *
        (1 + 2 * (0.281670034230 + 0.011720267591) / (0.560508144282 * 113.145923479372))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12802]

end BstLean.Part269.N12802

/-! The original eight local profiles supply actual 12802 moment certificates. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12802 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052623206929 ∧
    0 ≤ bN 12802 BstLean.Part154.csC (groupTheta g) ∧ bN 12802 BstLean.Part154.csC (groupTheta g) ≤ 0.001368994743 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12802 12802 0.011
      (momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12802 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12802 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12802 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229397486754 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12802 0.011
      (momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12802 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12802
/-! The actual computed-centre upper energy formula at 12802. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12802

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12802)
open BstLean.Part268 (cell12802)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085198244869
  | 2 => 0.086135750692
  | 3 => 0.087070650991
  | 4 => 0.088004190805
  | 5 => 0.088937881560
  | 6 => 0.089873541333
  | 7 => 0.090813339040
  | 8 => 0.091759842607
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12802 12802 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12802 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12802

/-! Actual upper energy certificates on all 43 source endpoints at 12802. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12802)
open BstLean.Part268 (cell12802)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12802 (gMinus 12802) (1 - (cell12802 i).lower) ≤ 1 ∧
    energyUpper 12802 (gMinus 12802) (BstLean.Part211.gPlus 12802)
      (finiteEnergy 12802 12802 0.011) (1 - (cell12802 i).lower) ≤
      (cell12802 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨10,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨11,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨12,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨13,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨14,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨15,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨16,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨17,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨18,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨19,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨20,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨21,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨22,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨23,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨24,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨25,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨26,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨27,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨28,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨29,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨30,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨31,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨32,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨33,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨34,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨35,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨36,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨37,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨38,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨39,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨40,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨41,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨42,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨43,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨44,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨45,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨46,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨47,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨48,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨49,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨50,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨51,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12802) (by norm_num)
        (q := 1 - (cell12802 ⟨52,by decide⟩).lower)
        (by norm_num [cell12802]) (by norm_num [cell12802])
      exact ⟨E.1,E.2.trans (by norm_num [cell12802])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12802

/-! Source-cell containment and simple scalar guards at 12802. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12802)
open BstLean.Part268 (cell12802)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12802 ⟨10,by decide⟩).lower ∧ (cell12802 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12802 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12802 ⟨11,by decide⟩).lower ∧ (cell12802 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12802 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12802 ⟨12,by decide⟩).lower ∧ (cell12802 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12802 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12802 ⟨13,by decide⟩).lower ∧ (cell12802 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12802 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12802 ⟨14,by decide⟩).lower ∧ (cell12802 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12802 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12802 ⟨15,by decide⟩).lower ∧ (cell12802 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12802 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12802 ⟨16,by decide⟩).lower ∧ (cell12802 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12802 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12802 ⟨17,by decide⟩).lower ∧ (cell12802 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12802 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12802 ⟨18,by decide⟩).lower ∧ (cell12802 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12802 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12802 ⟨19,by decide⟩).lower ∧ (cell12802 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12802 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12802 ⟨20,by decide⟩).lower ∧ (cell12802 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12802 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12802 ⟨21,by decide⟩).lower ∧ (cell12802 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12802 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12802 ⟨22,by decide⟩).lower ∧ (cell12802 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12802 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12802 ⟨23,by decide⟩).lower ∧ (cell12802 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12802 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12802 ⟨24,by decide⟩).lower ∧ (cell12802 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12802 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12802 ⟨25,by decide⟩).lower ∧ (cell12802 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12802 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12802 ⟨26,by decide⟩).lower ∧ (cell12802 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12802 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12802 ⟨27,by decide⟩).lower ∧ (cell12802 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12802 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12802 ⟨28,by decide⟩).lower ∧ (cell12802 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12802 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12802 ⟨29,by decide⟩).lower ∧ (cell12802 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12802 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12802 ⟨30,by decide⟩).lower ∧ (cell12802 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12802 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12802 ⟨31,by decide⟩).lower ∧ (cell12802 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12802 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12802 ⟨32,by decide⟩).lower ∧ (cell12802 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12802 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12802 ⟨33,by decide⟩).lower ∧ (cell12802 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12802 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12802 ⟨34,by decide⟩).lower ∧ (cell12802 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12802 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12802 ⟨35,by decide⟩).lower ∧ (cell12802 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12802 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12802 ⟨36,by decide⟩).lower ∧ (cell12802 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12802 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12802 ⟨37,by decide⟩).lower ∧ (cell12802 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12802 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12802 ⟨38,by decide⟩).lower ∧ (cell12802 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12802 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12802 ⟨39,by decide⟩).lower ∧ (cell12802 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12802 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12802 ⟨40,by decide⟩).lower ∧ (cell12802 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12802 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12802 ⟨41,by decide⟩).lower ∧ (cell12802 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12802 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12802 ⟨42,by decide⟩).lower ∧ (cell12802 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12802 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12802 ⟨43,by decide⟩).lower ∧ (cell12802 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12802 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12802 ⟨44,by decide⟩).lower ∧ (cell12802 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12802 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12802 ⟨45,by decide⟩).lower ∧ (cell12802 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12802 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12802 ⟨46,by decide⟩).lower ∧ (cell12802 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12802 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12802 ⟨47,by decide⟩).lower ∧ (cell12802 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12802 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12802 ⟨48,by decide⟩).lower ∧ (cell12802 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12802 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12802 ⟨49,by decide⟩).lower ∧ (cell12802 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12802 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12802 ⟨50,by decide⟩).lower ∧ (cell12802 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12802 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12802 ⟨51,by decide⟩).lower ∧ (cell12802 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12802 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12802 ⟨52,by decide⟩).lower ∧ (cell12802 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12802 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12802 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12802 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12802,cell12802,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12802 i).lower ∧
    (cell12802 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12802 i).upper ≤ (0.532 : ℝ) ∧
    (cell12802 i).centre ≤ (0.1 : ℝ) ∧ (cell12802 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12802 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12802 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12802

/-! The local source numeric instances at 12802 have no network premises. -/
namespace BstLean.Part269.N12802
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12802)
open BstLean.Part268 (cell12802)

noncomputable def sourceNumerics12802 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12802 (cell12802 i)
      scalarRow12802.M scalarRow12802.H scalarRow12802.xi := by
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
    energy_allowance := scalarRow12802.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12802]
    centre_nonneg := (scalarRow12802.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12802])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12802
/-! Actual 12803 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12803 ≤ (1.035663623359 : ℝ) := by
  have hr : (113.150342465235 : ℝ) ≤ √(12803 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.150342465235 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12803 12803 (11 / 1000) ≤
    (0.008447937308 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12803) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.150342465235 : ℝ) ≤ √(12803 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12803)
  have hdiv : K / √(12803 : ℝ) ≤ K / 113.150342465235 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.150342465235 ≤ (0.008447937308 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12803.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12803 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12803 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12803 := gPlus_lower 12803
end BstLean.Part269.N12803

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12803
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035663623358 : ℝ) ≤ wn 12803 := by
  have hn : √(12803 : ℝ) ≤ 113.150342465236 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12803 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.150342465236 ≤ 2 / √(12803 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249819369 : ℝ) ≤ rhoBar 12803 BstLean.Part154.csC ∧
    rhoBar 12803 BstLean.Part154.csC ≤ 0.000249819756 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035663623358 : ℝ) / (1.295212 * 12803) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035663623359 : ℝ) / (1.29521 * 12803) := by gcongr
      _ ≤ (0.000249819756 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12803 BstLean.Part154.csC) ≤ 0.000999341434 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12803 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) ≤ 0.000190813942 ∧
    cc1 (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) ≤ 0.000121416193 ∧
    cc2 (rhoBar 12803 BstLean.Part154.csC) ≤ 0.000070483049 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12803 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12803 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12803 BstLean.Part154.csC * nuR (rhoBar 12803 BstLean.Part154.csC)) ≤ 0.000499655115 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249819756 : ℝ) * 0.000999341434 := by gcongr
      _ ≤ (0.000499655115 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12803 BstLean.Part154.csC) * nuR (rhoBar 12803 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999341434 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12803 BstLean.Part154.csC) * rhoBar 12803 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249819756 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249819756 / 2 + 0.399 * 0.000999341434 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190813942 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499655115 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121416193 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249819756 / 1.414213562 := by gcongr
      _ ≤ (0.000070483049 : ℝ) := by norm_num

end BstLean.Part269.N12803

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12803
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) ≤ 1.57237E-7 := by
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12803 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12803 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12803 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190813942 : ℝ) ^ 2 + 0.000121416193 ^ 2 + 3 * 0.000070483049 ^ 2 +
        2 * 0.797885 * 0.000190813942 * 0.000121416193 + 2 * 0.000190813942 * 0.000070483049 +
        4 * 0.797885 * 0.000121416193 * 0.000070483049 := by gcongr
    _ ≤ (1.57237E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12803 BstLean.Part154.csC Θ ≤ 0.002607398167 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12803 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12803 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12803 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035663623359 * 1.57237E-7 / (0.000249819369 : ℝ) := by gcongr
    _ ≤ 0.002607398167 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12803 BstLean.Part154.csC Θ ≤ 0.002892646410 + 0.000658848721 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12803 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12803 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035663623359 : ℝ) * ((2 * Θ * 0.000249819756 +
        (6863 / 10000) * 0.000249819756 * 12803 * 0.000999341434) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002892646410 + 0.000658848721 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12803 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12803 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12803 0.011 Θ ∧ gammaRatio 12803 0.011 Θ ≤ 0.000085881572 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12803 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035663623359 : ℝ) * 0.525 / ((1 - 0.011) * 12803) := by gcongr
      _ ≤ (0.000085881572 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12803 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12803 0.011 Θ) :=
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
    badAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12803 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12803 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12803 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12803 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12803 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12803 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12803 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12803 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12803 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12803 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035663623359 : ℝ) * 12803 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003401450910 + 0.003266246888 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12803

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12803
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12803 BstLean.Part154.csC) (piBar (rhoBar 12803 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12803 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12803 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12803 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12803 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12803 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12803 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12803 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12803 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12803 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12803 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052270483970 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12803) ≤ 0.010554431874 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12803 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035663623359)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010554431874 + 2 * 0.737676 / 12803) := by gcongr
    _ ≤ (0.052270483970 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12803 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12803

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12803
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508188783 : ℝ) ≤ plow 12803 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12803) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622830527)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368884038) : eMP 12803 0.011 xi bn ≤ 0.001178615193 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12803 : ℝ) * (1 - 0.011))) ≤ 0.000582779507 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368884038 / (12803 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582779507 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582779507 : ℝ) + 3.141593 * 0.052622830527 / (12803 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178615193 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622830527)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368884038) : PiBarMP 12803 12 0.011 xi bn ≤ 0.160594319812 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12803 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036998432913 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.526294704837 : ℝ) ≤ √((12803 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.150342465235 : ℝ) ≤ √(12803 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12803) ≤ 0.123131825846 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036998432913 + 0.052622830527 * 1.772454 / (2 * (112.526294704837 : ℝ))) * (1 + 0.001178615193) +
        8 / (12803 * 113.150342465235) + 0.123131825846 := by gcongr
    _ ≤ (0.160594319812 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622830527)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368884038) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281667150309) :
    parallelOracle 12803 0.011 xi bn cd ≤ 0.161576401188 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12803 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12803 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508188783 : ℝ) ≤ plow 12803 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.150342465235 : ℝ) ≤ √(12803 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281667150309 : ℝ) / (2 * 0.560508188783 * 113.150342465235)) * 0.160594319812 +
        0.281667150309 ^ 2 / (2 * 0.560508188783 * 113.150342465235) := by gcongr
    _ ≤ (0.161576401188 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622830527) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368884038)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281667150309) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12803 12803 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508188783 : ℝ) ≤ plow 12803 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.150342465235 : ℝ) ≤ √(12803 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12803 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12803 Θ 1.22 ≤ 0.011719809867 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.150342465235 := by gcongr <;> linarith
      _ ≤ (0.011719809867 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12803 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12803 12803 0.011 ≤ 0.008447937308 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12803 12803 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12803 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12803 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12803 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12803 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161576401188 + 0.011719809867 + (0.008447937308 : ℝ) *
        (1 + 2 * (0.281667150309 + 0.011719809867) / (0.560508188783 * 113.150342465235))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12803]

end BstLean.Part269.N12803

/-! The original eight local profiles supply actual 12803 moment certificates. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12803 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052622830527 ∧
    0 ≤ bN 12803 BstLean.Part154.csC (groupTheta g) ∧ bN 12803 BstLean.Part154.csC (groupTheta g) ≤ 0.001368884038 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12803 12803 0.011
      (momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12803 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12803 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12803 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229396666339 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12803 0.011
      (momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12803 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12803
/-! The actual computed-centre upper energy formula at 12803. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12803

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12803)
open BstLean.Part268 (cell12803)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085195434157
  | 2 => 0.086132890672
  | 3 => 0.087067734851
  | 4 => 0.088001210139
  | 5 => 0.088934826079
  | 6 => 0.089870398546
  | 7 => 0.090810093891
  | 8 => 0.091756477074
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12803 12803 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12803 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12803

/-! Actual upper energy certificates on all 43 source endpoints at 12803. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12803)
open BstLean.Part268 (cell12803)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12803 (gMinus 12803) (1 - (cell12803 i).lower) ≤ 1 ∧
    energyUpper 12803 (gMinus 12803) (BstLean.Part211.gPlus 12803)
      (finiteEnergy 12803 12803 0.011) (1 - (cell12803 i).lower) ≤
      (cell12803 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨10,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨11,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨12,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨13,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨14,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨15,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨16,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨17,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨18,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨19,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨20,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨21,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨22,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨23,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨24,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨25,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨26,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨27,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨28,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨29,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨30,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨31,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨32,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨33,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨34,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨35,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨36,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨37,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨38,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨39,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨40,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨41,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨42,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨43,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨44,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨45,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨46,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨47,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨48,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨49,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨50,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨51,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12803) (by norm_num)
        (q := 1 - (cell12803 ⟨52,by decide⟩).lower)
        (by norm_num [cell12803]) (by norm_num [cell12803])
      exact ⟨E.1,E.2.trans (by norm_num [cell12803])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12803

/-! Source-cell containment and simple scalar guards at 12803. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12803)
open BstLean.Part268 (cell12803)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12803 ⟨10,by decide⟩).lower ∧ (cell12803 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12803 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12803 ⟨11,by decide⟩).lower ∧ (cell12803 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12803 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12803 ⟨12,by decide⟩).lower ∧ (cell12803 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12803 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12803 ⟨13,by decide⟩).lower ∧ (cell12803 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12803 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12803 ⟨14,by decide⟩).lower ∧ (cell12803 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12803 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12803 ⟨15,by decide⟩).lower ∧ (cell12803 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12803 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12803 ⟨16,by decide⟩).lower ∧ (cell12803 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12803 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12803 ⟨17,by decide⟩).lower ∧ (cell12803 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12803 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12803 ⟨18,by decide⟩).lower ∧ (cell12803 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12803 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12803 ⟨19,by decide⟩).lower ∧ (cell12803 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12803 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12803 ⟨20,by decide⟩).lower ∧ (cell12803 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12803 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12803 ⟨21,by decide⟩).lower ∧ (cell12803 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12803 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12803 ⟨22,by decide⟩).lower ∧ (cell12803 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12803 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12803 ⟨23,by decide⟩).lower ∧ (cell12803 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12803 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12803 ⟨24,by decide⟩).lower ∧ (cell12803 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12803 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12803 ⟨25,by decide⟩).lower ∧ (cell12803 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12803 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12803 ⟨26,by decide⟩).lower ∧ (cell12803 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12803 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12803 ⟨27,by decide⟩).lower ∧ (cell12803 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12803 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12803 ⟨28,by decide⟩).lower ∧ (cell12803 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12803 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12803 ⟨29,by decide⟩).lower ∧ (cell12803 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12803 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12803 ⟨30,by decide⟩).lower ∧ (cell12803 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12803 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12803 ⟨31,by decide⟩).lower ∧ (cell12803 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12803 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12803 ⟨32,by decide⟩).lower ∧ (cell12803 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12803 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12803 ⟨33,by decide⟩).lower ∧ (cell12803 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12803 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12803 ⟨34,by decide⟩).lower ∧ (cell12803 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12803 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12803 ⟨35,by decide⟩).lower ∧ (cell12803 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12803 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12803 ⟨36,by decide⟩).lower ∧ (cell12803 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12803 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12803 ⟨37,by decide⟩).lower ∧ (cell12803 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12803 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12803 ⟨38,by decide⟩).lower ∧ (cell12803 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12803 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12803 ⟨39,by decide⟩).lower ∧ (cell12803 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12803 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12803 ⟨40,by decide⟩).lower ∧ (cell12803 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12803 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12803 ⟨41,by decide⟩).lower ∧ (cell12803 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12803 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12803 ⟨42,by decide⟩).lower ∧ (cell12803 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12803 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12803 ⟨43,by decide⟩).lower ∧ (cell12803 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12803 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12803 ⟨44,by decide⟩).lower ∧ (cell12803 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12803 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12803 ⟨45,by decide⟩).lower ∧ (cell12803 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12803 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12803 ⟨46,by decide⟩).lower ∧ (cell12803 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12803 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12803 ⟨47,by decide⟩).lower ∧ (cell12803 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12803 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12803 ⟨48,by decide⟩).lower ∧ (cell12803 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12803 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12803 ⟨49,by decide⟩).lower ∧ (cell12803 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12803 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12803 ⟨50,by decide⟩).lower ∧ (cell12803 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12803 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12803 ⟨51,by decide⟩).lower ∧ (cell12803 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12803 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12803 ⟨52,by decide⟩).lower ∧ (cell12803 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12803 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12803 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12803 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12803,cell12803,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12803 i).lower ∧
    (cell12803 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12803 i).upper ≤ (0.532 : ℝ) ∧
    (cell12803 i).centre ≤ (0.1 : ℝ) ∧ (cell12803 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12803 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12803 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12803

/-! The local source numeric instances at 12803 have no network premises. -/
namespace BstLean.Part269.N12803
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12803)
open BstLean.Part268 (cell12803)

noncomputable def sourceNumerics12803 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12803 (cell12803 i)
      scalarRow12803.M scalarRow12803.H scalarRow12803.xi := by
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
    energy_allowance := scalarRow12803.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12803]
    centre_nonneg := (scalarRow12803.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12803])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12803
/-! Actual 12804 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12804 ≤ (1.035662218457 : ℝ) := by
  have hr : (113.154761278525 : ℝ) ≤ √(12804 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.154761278525 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12804 12804 (11 / 1000) ≤
    (0.008447607405 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12804) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.154761278525 : ℝ) ≤ √(12804 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12804)
  have hdiv : K / √(12804 : ℝ) ≤ K / 113.154761278525 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.154761278525 ≤ (0.008447607405 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12804.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12804 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12804 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12804 := gPlus_lower 12804
end BstLean.Part269.N12804

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12804
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035662218456 : ℝ) ≤ wn 12804 := by
  have hn : √(12804 : ℝ) ≤ 113.154761278526 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12804 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.154761278526 ≤ 2 / √(12804 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249799520 : ℝ) ≤ rhoBar 12804 BstLean.Part154.csC ∧
    rhoBar 12804 BstLean.Part154.csC ≤ 0.000249799906 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035662218456 : ℝ) / (1.295212 * 12804) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035662218457 : ℝ) / (1.29521 * 12804) := by gcongr
      _ ≤ (0.000249799906 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12804 BstLean.Part154.csC) ≤ 0.000999262024 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12804 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) ≤ 0.000190798780 ∧
    cc1 (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) ≤ 0.000121406546 ∧
    cc2 (rhoBar 12804 BstLean.Part154.csC) ≤ 0.000070477448 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12804 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12804 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12804 BstLean.Part154.csC * nuR (rhoBar 12804 BstLean.Part154.csC)) ≤ 0.000499615412 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249799906 : ℝ) * 0.000999262024 := by gcongr
      _ ≤ (0.000499615412 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12804 BstLean.Part154.csC) * nuR (rhoBar 12804 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999262024 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12804 BstLean.Part154.csC) * rhoBar 12804 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249799906 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249799906 / 2 + 0.399 * 0.000999262024 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190798780 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499615412 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121406546 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249799906 / 1.414213562 := by gcongr
      _ ≤ (0.000070477448 : ℝ) := by norm_num

end BstLean.Part269.N12804

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12804
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) ≤ 1.57212E-7 := by
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12804 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12804 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12804 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190798780 : ℝ) ^ 2 + 0.000121406546 ^ 2 + 3 * 0.000070477448 ^ 2 +
        2 * 0.797885 * 0.000190798780 * 0.000121406546 + 2 * 0.000190798780 * 0.000070477448 +
        4 * 0.797885 * 0.000121406546 * 0.000070477448 := by gcongr
    _ ≤ (1.57212E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12804 BstLean.Part154.csC Θ ≤ 0.002607187215 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12804 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12804 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12804 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035662218457 * 1.57212E-7 / (0.000249799520 : ℝ) := by gcongr
    _ ≤ 0.002607187215 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12804 BstLean.Part154.csC Θ ≤ 0.002892408706 + 0.000658795477 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12804 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12804 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035662218457 : ℝ) * ((2 * Θ * 0.000249799906 +
        (6863 / 10000) * 0.000249799906 * 12804 * 0.000999262024) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002892408706 + 0.000658795477 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12804 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12804 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12804 0.011 Θ ∧ gammaRatio 12804 0.011 Θ ≤ 0.000085874748 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12804 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035662218457 : ℝ) * 0.525 / ((1 - 0.011) * 12804) := by gcongr
      _ ≤ (0.000085874748 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12804 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12804 0.011 Θ) :=
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
    badAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12804 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12804 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12804 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12804 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12804 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12804 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12804 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12804 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12804 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12804 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035662218457 : ℝ) * 12804 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003401213206 + 0.003265982692 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12804

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12804
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12804 BstLean.Part154.csC) (piBar (rhoBar 12804 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12804 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12804 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12804 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12804 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12804 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12804 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12804 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12804 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12804 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12804 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052268420712 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12804) ≤ 0.010554019713 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12804 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035662218457)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010554019713 + 2 * 0.737676 / 12804) := by gcongr
    _ ≤ (0.052268420712 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12804 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12804

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12804
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508233278 : ℝ) ≤ plow 12804 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12804) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622454120)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368773288) : eMP 12804 0.011 xi bn ≤ 0.001178521414 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12804 : ℝ) * (1 - 0.011))) ≤ 0.000582733174 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368773288 / (12804 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582733174 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582733174 : ℝ) + 3.141593 * 0.052622454120 / (12804 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178521414 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622454120)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368773288) : PiBarMP 12804 12 0.011 xi bn ≤ 0.160587989578 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12804 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036996936198 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.530689147449 : ℝ) ≤ √((12804 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.154761278525 : ℝ) ≤ √(12804 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12804) ≤ 0.123127017417 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036996936198 + 0.052622454120 * 1.772454 / (2 * (112.530689147449 : ℝ))) * (1 + 0.001178521414) +
        8 / (12804 * 113.154761278525) + 0.123127017417 := by gcongr
    _ ≤ (0.160587989578 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622454120)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368773288) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281664266621) :
    parallelOracle 12804 0.011 xi bn cd ≤ 0.161570002011 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12804 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12804 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508233278 : ℝ) ≤ plow 12804 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.154761278525 : ℝ) ≤ √(12804 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281664266621 : ℝ) / (2 * 0.560508233278 * 113.154761278525)) * 0.160587989578 +
        0.281664266621 ^ 2 / (2 * 0.560508233278 * 113.154761278525) := by gcongr
    _ ≤ (0.161570002011 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622454120) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368773288)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281664266621) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12804 12804 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508233278 : ℝ) ≤ plow 12804 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.154761278525 : ℝ) ≤ √(12804 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12804 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12804 Θ 1.22 ≤ 0.011719352196 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.154761278525 := by gcongr <;> linarith
      _ ≤ (0.011719352196 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12804 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12804 12804 0.011 ≤ 0.008447607405 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12804 12804 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12804 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12804 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12804 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12804 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161570002011 + 0.011719352196 + (0.008447607405 : ℝ) *
        (1 + 2 * (0.281664266621 + 0.011719352196) / (0.560508233278 * 113.154761278525))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12804]

end BstLean.Part269.N12804

/-! The original eight local profiles supply actual 12804 moment certificates. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12804 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052622454120 ∧
    0 ≤ bN 12804 BstLean.Part154.csC (groupTheta g) ∧ bN 12804 BstLean.Part154.csC (groupTheta g) ≤ 0.001368773288 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12804 12804 0.011
      (momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12804 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12804 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12804 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229395845909 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12804 0.011
      (momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12804 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12804
/-! The actual computed-centre upper energy formula at 12804. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12804

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12804)
open BstLean.Part268 (cell12804)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085192624423
  | 2 => 0.086130031669
  | 3 => 0.087064819776
  | 4 => 0.087998230596
  | 5 => 0.088931771794
  | 6 => 0.089867257043
  | 7 => 0.090806850133
  | 8 => 0.091753113062
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12804 12804 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12804 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12804

/-! Actual upper energy certificates on all 43 source endpoints at 12804. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12804)
open BstLean.Part268 (cell12804)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12804 (gMinus 12804) (1 - (cell12804 i).lower) ≤ 1 ∧
    energyUpper 12804 (gMinus 12804) (BstLean.Part211.gPlus 12804)
      (finiteEnergy 12804 12804 0.011) (1 - (cell12804 i).lower) ≤
      (cell12804 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨10,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨11,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨12,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨13,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨14,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨15,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨16,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨17,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨18,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨19,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨20,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨21,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨22,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨23,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨24,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨25,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨26,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨27,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨28,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨29,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨30,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨31,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨32,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨33,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨34,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨35,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨36,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨37,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨38,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨39,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨40,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨41,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨42,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨43,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨44,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨45,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨46,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨47,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨48,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨49,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨50,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨51,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12804) (by norm_num)
        (q := 1 - (cell12804 ⟨52,by decide⟩).lower)
        (by norm_num [cell12804]) (by norm_num [cell12804])
      exact ⟨E.1,E.2.trans (by norm_num [cell12804])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12804

/-! Source-cell containment and simple scalar guards at 12804. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12804)
open BstLean.Part268 (cell12804)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12804 ⟨10,by decide⟩).lower ∧ (cell12804 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12804 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12804 ⟨11,by decide⟩).lower ∧ (cell12804 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12804 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12804 ⟨12,by decide⟩).lower ∧ (cell12804 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12804 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12804 ⟨13,by decide⟩).lower ∧ (cell12804 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12804 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12804 ⟨14,by decide⟩).lower ∧ (cell12804 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12804 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12804 ⟨15,by decide⟩).lower ∧ (cell12804 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12804 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12804 ⟨16,by decide⟩).lower ∧ (cell12804 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12804 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12804 ⟨17,by decide⟩).lower ∧ (cell12804 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12804 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12804 ⟨18,by decide⟩).lower ∧ (cell12804 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12804 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12804 ⟨19,by decide⟩).lower ∧ (cell12804 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12804 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12804 ⟨20,by decide⟩).lower ∧ (cell12804 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12804 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12804 ⟨21,by decide⟩).lower ∧ (cell12804 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12804 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12804 ⟨22,by decide⟩).lower ∧ (cell12804 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12804 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12804 ⟨23,by decide⟩).lower ∧ (cell12804 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12804 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12804 ⟨24,by decide⟩).lower ∧ (cell12804 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12804 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12804 ⟨25,by decide⟩).lower ∧ (cell12804 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12804 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12804 ⟨26,by decide⟩).lower ∧ (cell12804 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12804 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12804 ⟨27,by decide⟩).lower ∧ (cell12804 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12804 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12804 ⟨28,by decide⟩).lower ∧ (cell12804 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12804 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12804 ⟨29,by decide⟩).lower ∧ (cell12804 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12804 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12804 ⟨30,by decide⟩).lower ∧ (cell12804 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12804 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12804 ⟨31,by decide⟩).lower ∧ (cell12804 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12804 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12804 ⟨32,by decide⟩).lower ∧ (cell12804 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12804 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12804 ⟨33,by decide⟩).lower ∧ (cell12804 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12804 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12804 ⟨34,by decide⟩).lower ∧ (cell12804 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12804 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12804 ⟨35,by decide⟩).lower ∧ (cell12804 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12804 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12804 ⟨36,by decide⟩).lower ∧ (cell12804 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12804 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12804 ⟨37,by decide⟩).lower ∧ (cell12804 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12804 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12804 ⟨38,by decide⟩).lower ∧ (cell12804 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12804 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12804 ⟨39,by decide⟩).lower ∧ (cell12804 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12804 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12804 ⟨40,by decide⟩).lower ∧ (cell12804 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12804 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12804 ⟨41,by decide⟩).lower ∧ (cell12804 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12804 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12804 ⟨42,by decide⟩).lower ∧ (cell12804 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12804 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12804 ⟨43,by decide⟩).lower ∧ (cell12804 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12804 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12804 ⟨44,by decide⟩).lower ∧ (cell12804 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12804 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12804 ⟨45,by decide⟩).lower ∧ (cell12804 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12804 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12804 ⟨46,by decide⟩).lower ∧ (cell12804 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12804 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12804 ⟨47,by decide⟩).lower ∧ (cell12804 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12804 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12804 ⟨48,by decide⟩).lower ∧ (cell12804 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12804 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12804 ⟨49,by decide⟩).lower ∧ (cell12804 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12804 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12804 ⟨50,by decide⟩).lower ∧ (cell12804 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12804 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12804 ⟨51,by decide⟩).lower ∧ (cell12804 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12804 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12804 ⟨52,by decide⟩).lower ∧ (cell12804 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12804 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12804 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12804 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12804,cell12804,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12804 i).lower ∧
    (cell12804 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12804 i).upper ≤ (0.532 : ℝ) ∧
    (cell12804 i).centre ≤ (0.1 : ℝ) ∧ (cell12804 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12804 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12804 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12804

/-! The local source numeric instances at 12804 have no network premises. -/
namespace BstLean.Part269.N12804
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12804)
open BstLean.Part268 (cell12804)

noncomputable def sourceNumerics12804 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12804 (cell12804 i)
      scalarRow12804.M scalarRow12804.H scalarRow12804.xi := by
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
    energy_allowance := scalarRow12804.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12804]
    centre_nonneg := (scalarRow12804.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12804])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12804
/-! Actual 12805 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12805 ≤ (1.035660813720 : ℝ) := by
  have hr : (113.159179919262 : ℝ) ≤ √(12805 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.159179919262 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12805 12805 (11 / 1000) ≤
    (0.008447277540 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12805) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.159179919262 : ℝ) ≤ √(12805 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12805)
  have hdiv : K / √(12805 : ℝ) ≤ K / 113.159179919262 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.159179919262 ≤ (0.008447277540 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12805.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12805 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12805 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12805 := gPlus_lower 12805
end BstLean.Part269.N12805

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12805
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035660813719 : ℝ) ≤ wn 12805 := by
  have hn : √(12805 : ℝ) ≤ 113.159179919263 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12805 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.159179919263 ≤ 2 / √(12805 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249779673 : ℝ) ≤ rhoBar 12805 BstLean.Part154.csC ∧
    rhoBar 12805 BstLean.Part154.csC ≤ 0.000249780059 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035660813719 : ℝ) / (1.295212 * 12805) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035660813720 : ℝ) / (1.29521 * 12805) := by gcongr
      _ ≤ (0.000249780059 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12805 BstLean.Part154.csC) ≤ 0.000999182627 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12805 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) ≤ 0.000190783620 ∧
    cc1 (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) ≤ 0.000121396899 ∧
    cc2 (rhoBar 12805 BstLean.Part154.csC) ≤ 0.000070471849 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12805 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12805 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12805 BstLean.Part154.csC * nuR (rhoBar 12805 BstLean.Part154.csC)) ≤ 0.000499575716 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249780059 : ℝ) * 0.000999182627 := by gcongr
      _ ≤ (0.000499575716 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12805 BstLean.Part154.csC) * nuR (rhoBar 12805 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999182627 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12805 BstLean.Part154.csC) * rhoBar 12805 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249780059 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249780059 / 2 + 0.399 * 0.000999182627 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190783620 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499575716 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121396899 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249780059 / 1.414213562 := by gcongr
      _ ≤ (0.000070471849 : ℝ) := by norm_num

end BstLean.Part269.N12805

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12805
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) ≤ 1.57187E-7 := by
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12805 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12805 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12805 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190783620 : ℝ) ^ 2 + 0.000121396899 ^ 2 + 3 * 0.000070471849 ^ 2 +
        2 * 0.797885 * 0.000190783620 * 0.000121396899 + 2 * 0.000190783620 * 0.000070471849 +
        4 * 0.797885 * 0.000121396899 * 0.000070471849 := by gcongr
    _ ≤ (1.57187E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12805 BstLean.Part154.csC Θ ≤ 0.002606976211 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12805 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12805 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12805 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035660813720 * 1.57187E-7 / (0.000249779673 : ℝ) := by gcongr
    _ ≤ 0.002606976211 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12805 BstLean.Part154.csC Θ ≤ 0.002892171040 + 0.000658742241 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12805 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12805 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035660813720 : ℝ) * ((2 * Θ * 0.000249780059 +
        (6863 / 10000) * 0.000249780059 * 12805 * 0.000999182627) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002892171040 + 0.000658742241 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12805 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12805 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12805 0.011 Θ ∧ gammaRatio 12805 0.011 Θ ≤ 0.000085867926 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12805 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035660813720 : ℝ) * 0.525 / ((1 - 0.011) * 12805) := by gcongr
      _ ≤ (0.000085867926 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12805 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12805 0.011 Θ) :=
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
    badAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12805 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12805 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12805 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12805 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12805 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12805 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12805 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12805 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12805 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12805 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035660813720 : ℝ) * 12805 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003400975540 + 0.003265718452 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12805

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12805
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12805 BstLean.Part154.csC) (piBar (rhoBar 12805 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12805 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12805 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12805 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12805 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12805 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12805 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12805 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12805 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12805 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12805 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052266357690 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12805) ≤ 0.010553607599 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12805 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035660813720)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010553607599 + 2 * 0.737676 / 12805) := by gcongr
    _ ≤ (0.052266357690 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12805 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12805

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12805
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508277766 : ℝ) ≤ plow 12805 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12805) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622077728)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368662511) : eMP 12805 0.011 xi bn ≤ 0.001178427633 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12805 : ℝ) * (1 - 0.011))) ≤ 0.000582686840 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368662511 / (12805 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582686840 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582686840 : ℝ) + 3.141593 * 0.052622077728 / (12805 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178427633 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622077728)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368662511) : PiBarMP 12805 12 0.011 xi bn ≤ 0.160581659484 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12805 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036995439057 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.535083418461 : ℝ) ≤ √((12805 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.159179919262 : ℝ) ≤ √(12805 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12805) ≤ 0.123122209553 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036995439057 + 0.052622077728 * 1.772454 / (2 * (112.535083418461 : ℝ))) * (1 + 0.001178427633) +
        8 / (12805 * 113.159179919262) + 0.123122209553 := by gcongr
    _ ≤ (0.160581659484 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622077728)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368662511) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281661383199) :
    parallelOracle 12805 0.011 xi bn cd ≤ 0.161563602984 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12805 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12805 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508277766 : ℝ) ≤ plow 12805 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.159179919262 : ℝ) ≤ √(12805 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281661383199 : ℝ) / (2 * 0.560508277766 * 113.159179919262)) * 0.160581659484 +
        0.281661383199 ^ 2 / (2 * 0.560508277766 * 113.159179919262) := by gcongr
    _ ≤ (0.161563602984 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052622077728) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368662511)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281661383199) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12805 12805 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508277766 : ℝ) ≤ plow 12805 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.159179919262 : ℝ) ≤ √(12805 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12805 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12805 Θ 1.22 ≤ 0.011718894578 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.159179919262 := by gcongr <;> linarith
      _ ≤ (0.011718894578 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12805 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12805 12805 0.011 ≤ 0.008447277540 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12805 12805 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12805 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12805 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12805 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12805 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161563602984 + 0.011718894578 + (0.008447277540 : ℝ) *
        (1 + 2 * (0.281661383199 + 0.011718894578) / (0.560508277766 * 113.159179919262))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12805]

end BstLean.Part269.N12805

/-! The original eight local profiles supply actual 12805 moment certificates. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12805 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052622077728 ∧
    0 ≤ bN 12805 BstLean.Part154.csC (groupTheta g) ∧ bN 12805 BstLean.Part154.csC (groupTheta g) ≤ 0.001368662511 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12805 12805 0.011
      (momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12805 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12805 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12805 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229395025509 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12805 0.011
      (momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12805 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12805
/-! The actual computed-centre upper energy formula at 12805. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12805

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12805)
open BstLean.Part268 (cell12805)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085189815666
  | 2 => 0.086127173682
  | 3 => 0.087061905765
  | 4 => 0.087995252177
  | 5 => 0.088928718705
  | 6 => 0.089864116824
  | 7 => 0.090803607766
  | 8 => 0.091749750567
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12805 12805 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12805 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12805

/-! Actual upper energy certificates on all 43 source endpoints at 12805. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12805)
open BstLean.Part268 (cell12805)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12805 (gMinus 12805) (1 - (cell12805 i).lower) ≤ 1 ∧
    energyUpper 12805 (gMinus 12805) (BstLean.Part211.gPlus 12805)
      (finiteEnergy 12805 12805 0.011) (1 - (cell12805 i).lower) ≤
      (cell12805 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨10,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨11,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨12,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨13,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨14,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨15,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨16,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨17,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨18,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨19,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨20,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨21,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨22,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨23,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨24,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨25,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨26,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨27,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨28,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨29,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨30,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨31,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨32,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨33,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨34,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨35,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨36,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨37,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨38,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨39,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨40,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨41,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨42,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨43,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨44,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨45,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨46,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨47,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨48,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨49,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨50,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨51,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12805) (by norm_num)
        (q := 1 - (cell12805 ⟨52,by decide⟩).lower)
        (by norm_num [cell12805]) (by norm_num [cell12805])
      exact ⟨E.1,E.2.trans (by norm_num [cell12805])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12805

/-! Source-cell containment and simple scalar guards at 12805. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12805)
open BstLean.Part268 (cell12805)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12805 ⟨10,by decide⟩).lower ∧ (cell12805 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12805 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12805 ⟨11,by decide⟩).lower ∧ (cell12805 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12805 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12805 ⟨12,by decide⟩).lower ∧ (cell12805 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12805 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12805 ⟨13,by decide⟩).lower ∧ (cell12805 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12805 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12805 ⟨14,by decide⟩).lower ∧ (cell12805 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12805 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12805 ⟨15,by decide⟩).lower ∧ (cell12805 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12805 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12805 ⟨16,by decide⟩).lower ∧ (cell12805 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12805 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12805 ⟨17,by decide⟩).lower ∧ (cell12805 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12805 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12805 ⟨18,by decide⟩).lower ∧ (cell12805 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12805 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12805 ⟨19,by decide⟩).lower ∧ (cell12805 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12805 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12805 ⟨20,by decide⟩).lower ∧ (cell12805 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12805 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12805 ⟨21,by decide⟩).lower ∧ (cell12805 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12805 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12805 ⟨22,by decide⟩).lower ∧ (cell12805 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12805 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12805 ⟨23,by decide⟩).lower ∧ (cell12805 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12805 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12805 ⟨24,by decide⟩).lower ∧ (cell12805 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12805 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12805 ⟨25,by decide⟩).lower ∧ (cell12805 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12805 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12805 ⟨26,by decide⟩).lower ∧ (cell12805 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12805 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12805 ⟨27,by decide⟩).lower ∧ (cell12805 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12805 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12805 ⟨28,by decide⟩).lower ∧ (cell12805 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12805 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12805 ⟨29,by decide⟩).lower ∧ (cell12805 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12805 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12805 ⟨30,by decide⟩).lower ∧ (cell12805 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12805 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12805 ⟨31,by decide⟩).lower ∧ (cell12805 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12805 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12805 ⟨32,by decide⟩).lower ∧ (cell12805 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12805 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12805 ⟨33,by decide⟩).lower ∧ (cell12805 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12805 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12805 ⟨34,by decide⟩).lower ∧ (cell12805 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12805 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12805 ⟨35,by decide⟩).lower ∧ (cell12805 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12805 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12805 ⟨36,by decide⟩).lower ∧ (cell12805 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12805 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12805 ⟨37,by decide⟩).lower ∧ (cell12805 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12805 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12805 ⟨38,by decide⟩).lower ∧ (cell12805 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12805 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12805 ⟨39,by decide⟩).lower ∧ (cell12805 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12805 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12805 ⟨40,by decide⟩).lower ∧ (cell12805 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12805 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12805 ⟨41,by decide⟩).lower ∧ (cell12805 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12805 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12805 ⟨42,by decide⟩).lower ∧ (cell12805 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12805 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12805 ⟨43,by decide⟩).lower ∧ (cell12805 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12805 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12805 ⟨44,by decide⟩).lower ∧ (cell12805 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12805 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12805 ⟨45,by decide⟩).lower ∧ (cell12805 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12805 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12805 ⟨46,by decide⟩).lower ∧ (cell12805 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12805 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12805 ⟨47,by decide⟩).lower ∧ (cell12805 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12805 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12805 ⟨48,by decide⟩).lower ∧ (cell12805 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12805 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12805 ⟨49,by decide⟩).lower ∧ (cell12805 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12805 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12805 ⟨50,by decide⟩).lower ∧ (cell12805 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12805 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12805 ⟨51,by decide⟩).lower ∧ (cell12805 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12805 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12805 ⟨52,by decide⟩).lower ∧ (cell12805 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12805 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12805 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12805 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12805,cell12805,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12805 i).lower ∧
    (cell12805 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12805 i).upper ≤ (0.532 : ℝ) ∧
    (cell12805 i).centre ≤ (0.1 : ℝ) ∧ (cell12805 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12805 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12805 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12805

/-! The local source numeric instances at 12805 have no network premises. -/
namespace BstLean.Part269.N12805
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12805)
open BstLean.Part268 (cell12805)

noncomputable def sourceNumerics12805 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12805 (cell12805 i)
      scalarRow12805.M scalarRow12805.H scalarRow12805.xi := by
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
    energy_allowance := scalarRow12805.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12805]
    centre_nonneg := (scalarRow12805.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12805])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12805
/-! Actual 12806 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12806 ≤ (1.035659409149 : ℝ) := by
  have hr : (113.163598387467 : ℝ) ≤ √(12806 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.163598387467 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12806 12806 (11 / 1000) ≤
    (0.008446947714 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12806) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.163598387467 : ℝ) ≤ √(12806 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12806)
  have hdiv : K / √(12806 : ℝ) ≤ K / 113.163598387467 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.163598387467 ≤ (0.008446947714 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12806.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12806 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12806 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12806 := gPlus_lower 12806
end BstLean.Part269.N12806

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12806
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035659409148 : ℝ) ≤ wn 12806 := by
  have hn : √(12806 : ℝ) ≤ 113.163598387468 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12806 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.163598387468 ≤ 2 / √(12806 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249759829 : ℝ) ≤ rhoBar 12806 BstLean.Part154.csC ∧
    rhoBar 12806 BstLean.Part154.csC ≤ 0.000249760216 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035659409148 : ℝ) / (1.295212 * 12806) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035659409149 : ℝ) / (1.29521 * 12806) := by gcongr
      _ ≤ (0.000249760216 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12806 BstLean.Part154.csC) ≤ 0.000999103245 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12806 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) ≤ 0.000190768463 ∧
    cc1 (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) ≤ 0.000121387255 ∧
    cc2 (rhoBar 12806 BstLean.Part154.csC) ≤ 0.000070466250 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12806 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12806 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12806 BstLean.Part154.csC * nuR (rhoBar 12806 BstLean.Part154.csC)) ≤ 0.000499536028 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249760216 : ℝ) * 0.000999103245 := by gcongr
      _ ≤ (0.000499536028 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12806 BstLean.Part154.csC) * nuR (rhoBar 12806 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999103245 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12806 BstLean.Part154.csC) * rhoBar 12806 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249760216 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249760216 / 2 + 0.399 * 0.000999103245 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190768463 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499536028 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121387255 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249760216 / 1.414213562 := by gcongr
      _ ≤ (0.000070466250 : ℝ) := by norm_num

end BstLean.Part269.N12806

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12806
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) ≤ 1.57162E-7 := by
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12806 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12806 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12806 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190768463 : ℝ) ^ 2 + 0.000121387255 ^ 2 + 3 * 0.000070466250 ^ 2 +
        2 * 0.797885 * 0.000190768463 * 0.000121387255 + 2 * 0.000190768463 * 0.000070466250 +
        4 * 0.797885 * 0.000121387255 * 0.000070466250 := by gcongr
    _ ≤ (1.57162E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12806 BstLean.Part154.csC Θ ≤ 0.002606765143 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12806 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12806 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12806 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035659409149 * 1.57162E-7 / (0.000249759829 : ℝ) := by gcongr
    _ ≤ 0.002606765143 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12806 BstLean.Part154.csC Θ ≤ 0.002891933429 + 0.000658689016 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12806 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12806 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035659409149 : ℝ) * ((2 * Θ * 0.000249760216 +
        (6863 / 10000) * 0.000249760216 * 12806 * 0.000999103245) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002891933429 + 0.000658689016 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12806 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12806 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12806 0.011 Θ ∧ gammaRatio 12806 0.011 Θ ≤ 0.000085861104 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12806 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035659409149 : ℝ) * 0.525 / ((1 - 0.011) * 12806) := by gcongr
      _ ≤ (0.000085861104 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12806 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12806 0.011 Θ) :=
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
    badAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12806 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12806 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12806 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12806 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12806 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12806 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12806 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12806 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12806 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12806 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035659409149 : ℝ) * 12806 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003400737929 + 0.003265454159 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12806

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12806
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12806 BstLean.Part154.csC) (piBar (rhoBar 12806 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12806 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12806 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12806 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12806 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12806 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12806 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12806 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12806 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12806 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12806 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052264294915 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12806) ≤ 0.010553195534 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12806 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035659409149)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010553195534 + 2 * 0.737676 / 12806) := by gcongr
    _ ≤ (0.052264294915 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12806 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12806

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12806
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508322247 : ℝ) ≤ plow 12806 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12806) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621701363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368551701) : eMP 12806 0.011 xi bn ≤ 0.001178333843 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12806 : ℝ) * (1 - 0.011))) ≤ 0.000582640501 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368551701 / (12806 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582640501 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582640501 : ℝ) + 3.141593 * 0.052621701363 / (12806 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178333843 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621701363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368551701) : PiBarMP 12806 12 0.011 xi bn ≤ 0.160575329448 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12806 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036993941410 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.539477517891 : ℝ) ≤ √((12806 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.163598387467 : ℝ) ≤ √(12806 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12806) ≤ 0.123117402251 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036993941410 + 0.052621701363 * 1.772454 / (2 * (112.539477517891 : ℝ))) * (1 + 0.001178333843) +
        8 / (12806 * 113.163598387467) + 0.123117402251 := by gcongr
    _ ≤ (0.160575329448 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621701363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368551701) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281658500080) :
    parallelOracle 12806 0.011 xi bn cd ≤ 0.161557204023 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12806 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12806 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508322247 : ℝ) ≤ plow 12806 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.163598387467 : ℝ) ≤ √(12806 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281658500080 : ℝ) / (2 * 0.560508322247 * 113.163598387467)) * 0.160575329448 +
        0.281658500080 ^ 2 / (2 * 0.560508322247 * 113.163598387467) := by gcongr
    _ ≤ (0.161557204023 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621701363) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368551701)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281658500080) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12806 12806 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508322247 : ℝ) ≤ plow 12806 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.163598387467 : ℝ) ≤ √(12806 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12806 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12806 Θ 1.22 ≤ 0.011718437015 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.163598387467 := by gcongr <;> linarith
      _ ≤ (0.011718437015 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12806 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12806 12806 0.011 ≤ 0.008446947714 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12806 12806 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12806 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12806 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12806 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12806 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161557204023 + 0.011718437015 + (0.008446947714 : ℝ) *
        (1 + 2 * (0.281658500080 + 0.011718437015) / (0.560508322247 * 113.163598387467))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12806]

end BstLean.Part269.N12806

/-! The original eight local profiles supply actual 12806 moment certificates. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12806 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052621701363 ∧
    0 ≤ bN 12806 BstLean.Part154.csC (groupTheta g) ∧ bN 12806 BstLean.Part154.csC (groupTheta g) ≤ 0.001368551701 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12806 12806 0.011
      (momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12806 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12806 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12806 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229394205165 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12806 0.011
      (momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12806 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12806
/-! The actual computed-centre upper energy formula at 12806. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12806

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12806)
open BstLean.Part268 (cell12806)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085187007885
  | 2 => 0.086124316709
  | 3 => 0.087058992817
  | 4 => 0.087992274879
  | 5 => 0.088925666809
  | 6 => 0.089860977887
  | 7 => 0.090800366787
  | 8 => 0.091746389590
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12806 12806 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12806 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12806

/-! Actual upper energy certificates on all 43 source endpoints at 12806. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12806)
open BstLean.Part268 (cell12806)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12806 (gMinus 12806) (1 - (cell12806 i).lower) ≤ 1 ∧
    energyUpper 12806 (gMinus 12806) (BstLean.Part211.gPlus 12806)
      (finiteEnergy 12806 12806 0.011) (1 - (cell12806 i).lower) ≤
      (cell12806 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨10,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨11,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨12,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨13,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨14,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨15,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨16,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨17,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨18,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨19,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨20,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨21,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨22,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨23,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨24,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨25,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨26,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨27,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨28,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨29,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨30,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨31,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨32,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨33,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨34,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨35,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨36,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨37,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨38,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨39,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨40,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨41,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨42,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨43,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨44,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨45,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨46,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨47,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨48,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨49,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨50,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨51,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12806) (by norm_num)
        (q := 1 - (cell12806 ⟨52,by decide⟩).lower)
        (by norm_num [cell12806]) (by norm_num [cell12806])
      exact ⟨E.1,E.2.trans (by norm_num [cell12806])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12806

/-! Source-cell containment and simple scalar guards at 12806. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12806)
open BstLean.Part268 (cell12806)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12806 ⟨10,by decide⟩).lower ∧ (cell12806 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12806 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12806 ⟨11,by decide⟩).lower ∧ (cell12806 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12806 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12806 ⟨12,by decide⟩).lower ∧ (cell12806 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12806 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12806 ⟨13,by decide⟩).lower ∧ (cell12806 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12806 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12806 ⟨14,by decide⟩).lower ∧ (cell12806 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12806 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12806 ⟨15,by decide⟩).lower ∧ (cell12806 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12806 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12806 ⟨16,by decide⟩).lower ∧ (cell12806 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12806 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12806 ⟨17,by decide⟩).lower ∧ (cell12806 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12806 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12806 ⟨18,by decide⟩).lower ∧ (cell12806 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12806 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12806 ⟨19,by decide⟩).lower ∧ (cell12806 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12806 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12806 ⟨20,by decide⟩).lower ∧ (cell12806 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12806 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12806 ⟨21,by decide⟩).lower ∧ (cell12806 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12806 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12806 ⟨22,by decide⟩).lower ∧ (cell12806 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12806 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12806 ⟨23,by decide⟩).lower ∧ (cell12806 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12806 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12806 ⟨24,by decide⟩).lower ∧ (cell12806 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12806 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12806 ⟨25,by decide⟩).lower ∧ (cell12806 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12806 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12806 ⟨26,by decide⟩).lower ∧ (cell12806 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12806 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12806 ⟨27,by decide⟩).lower ∧ (cell12806 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12806 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12806 ⟨28,by decide⟩).lower ∧ (cell12806 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12806 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12806 ⟨29,by decide⟩).lower ∧ (cell12806 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12806 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12806 ⟨30,by decide⟩).lower ∧ (cell12806 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12806 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12806 ⟨31,by decide⟩).lower ∧ (cell12806 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12806 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12806 ⟨32,by decide⟩).lower ∧ (cell12806 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12806 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12806 ⟨33,by decide⟩).lower ∧ (cell12806 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12806 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12806 ⟨34,by decide⟩).lower ∧ (cell12806 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12806 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12806 ⟨35,by decide⟩).lower ∧ (cell12806 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12806 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12806 ⟨36,by decide⟩).lower ∧ (cell12806 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12806 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12806 ⟨37,by decide⟩).lower ∧ (cell12806 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12806 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12806 ⟨38,by decide⟩).lower ∧ (cell12806 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12806 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12806 ⟨39,by decide⟩).lower ∧ (cell12806 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12806 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12806 ⟨40,by decide⟩).lower ∧ (cell12806 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12806 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12806 ⟨41,by decide⟩).lower ∧ (cell12806 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12806 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12806 ⟨42,by decide⟩).lower ∧ (cell12806 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12806 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12806 ⟨43,by decide⟩).lower ∧ (cell12806 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12806 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12806 ⟨44,by decide⟩).lower ∧ (cell12806 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12806 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12806 ⟨45,by decide⟩).lower ∧ (cell12806 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12806 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12806 ⟨46,by decide⟩).lower ∧ (cell12806 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12806 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12806 ⟨47,by decide⟩).lower ∧ (cell12806 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12806 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12806 ⟨48,by decide⟩).lower ∧ (cell12806 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12806 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12806 ⟨49,by decide⟩).lower ∧ (cell12806 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12806 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12806 ⟨50,by decide⟩).lower ∧ (cell12806 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12806 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12806 ⟨51,by decide⟩).lower ∧ (cell12806 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12806 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12806 ⟨52,by decide⟩).lower ∧ (cell12806 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12806 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12806 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12806 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12806,cell12806,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12806 i).lower ∧
    (cell12806 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12806 i).upper ≤ (0.532 : ℝ) ∧
    (cell12806 i).centre ≤ (0.1 : ℝ) ∧ (cell12806 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12806 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12806 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12806

/-! The local source numeric instances at 12806 have no network premises. -/
namespace BstLean.Part269.N12806
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12806)
open BstLean.Part268 (cell12806)

noncomputable def sourceNumerics12806 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12806 (cell12806 i)
      scalarRow12806.M scalarRow12806.H scalarRow12806.xi := by
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
    energy_allowance := scalarRow12806.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12806]
    centre_nonneg := (scalarRow12806.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12806])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12806
/-! Actual 12807 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12807 ≤ (1.035658004743 : ℝ) := by
  have hr : (113.168016683160 : ℝ) ≤ √(12807 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.168016683160 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12807 12807 (11 / 1000) ≤
    (0.008446617926 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12807) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.168016683160 : ℝ) ≤ √(12807 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12807)
  have hdiv : K / √(12807 : ℝ) ≤ K / 113.168016683160 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.168016683160 ≤ (0.008446617926 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12807.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12807 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12807 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12807 := gPlus_lower 12807
end BstLean.Part269.N12807

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12807
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035658004742 : ℝ) ≤ wn 12807 := by
  have hn : √(12807 : ℝ) ≤ 113.168016683161 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12807 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.168016683161 ≤ 2 / √(12807 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249739989 : ℝ) ≤ rhoBar 12807 BstLean.Part154.csC ∧
    rhoBar 12807 BstLean.Part154.csC ≤ 0.000249740375 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035658004742 : ℝ) / (1.295212 * 12807) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035658004743 : ℝ) / (1.29521 * 12807) := by gcongr
      _ ≤ (0.000249740375 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12807 BstLean.Part154.csC) ≤ 0.000999023871 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12807 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) ≤ 0.000190753308 ∧
    cc1 (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) ≤ 0.000121377612 ∧
    cc2 (rhoBar 12807 BstLean.Part154.csC) ≤ 0.000070460652 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12807 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12807 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12807 BstLean.Part154.csC * nuR (rhoBar 12807 BstLean.Part154.csC)) ≤ 0.000499496343 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249740375 : ℝ) * 0.000999023871 := by gcongr
      _ ≤ (0.000499496343 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12807 BstLean.Part154.csC) * nuR (rhoBar 12807 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000999023871 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12807 BstLean.Part154.csC) * rhoBar 12807 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249740375 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249740375 / 2 + 0.399 * 0.000999023871 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190753308 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499496343 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121377612 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249740375 / 1.414213562 := by gcongr
      _ ≤ (0.000070460652 : ℝ) := by norm_num

end BstLean.Part269.N12807

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12807
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) ≤ 1.57137E-7 := by
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12807 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12807 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12807 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190753308 : ℝ) ^ 2 + 0.000121377612 ^ 2 + 3 * 0.000070460652 ^ 2 +
        2 * 0.797885 * 0.000190753308 * 0.000121377612 + 2 * 0.000190753308 * 0.000070460652 +
        4 * 0.797885 * 0.000121377612 * 0.000070460652 := by gcongr
    _ ≤ (1.57137E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12807 BstLean.Part154.csC Θ ≤ 0.002606554002 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12807 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12807 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12807 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035658004743 * 1.57137E-7 / (0.000249739989 : ℝ) := by gcongr
    _ ≤ 0.002606554002 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12807 BstLean.Part154.csC Θ ≤ 0.002891695830 + 0.000658635797 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12807 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12807 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035658004743 : ℝ) * ((2 * Θ * 0.000249740375 +
        (6863 / 10000) * 0.000249740375 * 12807 * 0.000999023871) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002891695830 + 0.000658635797 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12807 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12807 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12807 0.011 Θ ∧ gammaRatio 12807 0.011 Θ ≤ 0.000085854283 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12807 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035658004743 : ℝ) * 0.525 / ((1 - 0.011) * 12807) := by gcongr
      _ ≤ (0.000085854283 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12807 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12807 0.011 Θ) :=
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
    badAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12807 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12807 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12807 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12807 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12807 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12807 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12807 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12807 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12807 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12807 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035658004743 : ℝ) * 12807 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003400500330 + 0.003265189799 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12807

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12807
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12807 BstLean.Part154.csC) (piBar (rhoBar 12807 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12807 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12807 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12807 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12807 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12807 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12807 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12807 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12807 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12807 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12807 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052262232382 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12807) ≤ 0.010552783517 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12807 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035658004743)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010552783517 + 2 * 0.737676 / 12807) := by gcongr
    _ ≤ (0.052262232382 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12807 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12807

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12807
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508366721 : ℝ) ≤ plow 12807 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12807) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621324975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368440852) : eMP 12807 0.011 xi bn ≤ 0.001178240044 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12807 : ℝ) * (1 - 0.011))) ≤ 0.000582594158 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368440852 / (12807 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582594158 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582594158 : ℝ) + 3.141593 * 0.052621324975 / (12807 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178240044 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621324975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368440852) : PiBarMP 12807 12 0.011 xi bn ≤ 0.160568999389 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12807 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036992443175 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.543871445761 : ℝ) ≤ √((12807 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.168016683160 : ℝ) ≤ √(12807 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12807) ≤ 0.123112595512 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036992443175 + 0.052621324975 * 1.772454 / (2 * (112.543871445761 : ℝ))) * (1 + 0.001178240044) +
        8 / (12807 * 113.168016683160) + 0.123112595512 := by gcongr
    _ ≤ (0.160568999389 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621324975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368440852) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281655617150) :
    parallelOracle 12807 0.011 xi bn cd ≤ 0.161550805048 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12807 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12807 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508366721 : ℝ) ≤ plow 12807 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.168016683160 : ℝ) ≤ √(12807 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281655617150 : ℝ) / (2 * 0.560508366721 * 113.168016683160)) * 0.160568999389 +
        0.281655617150 ^ 2 / (2 * 0.560508366721 * 113.168016683160) := by gcongr
    _ ≤ (0.161550805048 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052621324975) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368440852)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281655617150) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12807 12807 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508366721 : ℝ) ≤ plow 12807 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.168016683160 : ℝ) ≤ √(12807 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12807 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12807 Θ 1.22 ≤ 0.011717979504 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.168016683160 := by gcongr <;> linarith
      _ ≤ (0.011717979504 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12807 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12807 12807 0.011 ≤ 0.008446617926 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12807 12807 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12807 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12807 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12807 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12807 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161550805048 + 0.011717979504 + (0.008446617926 : ℝ) *
        (1 + 2 * (0.281655617150 + 0.011717979504) / (0.560508366721 * 113.168016683160))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12807]

end BstLean.Part269.N12807

/-! The original eight local profiles supply actual 12807 moment certificates. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12807 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052621324975 ∧
    0 ≤ bN 12807 BstLean.Part154.csC (groupTheta g) ∧ bN 12807 BstLean.Part154.csC (groupTheta g) ≤ 0.001368440852 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12807 12807 0.011
      (momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12807 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12807 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12807 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229393384768 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12807 0.011
      (momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12807 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12807
/-! The actual computed-centre upper energy formula at 12807. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12807

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12807)
open BstLean.Part268 (cell12807)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085184201079
  | 2 => 0.086121460751
  | 3 => 0.087056080931
  | 4 => 0.087989298702
  | 5 => 0.088922616107
  | 6 => 0.089857840230
  | 7 => 0.090797127195
  | 8 => 0.091743030128
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12807 12807 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12807 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12807

/-! Actual upper energy certificates on all 43 source endpoints at 12807. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12807)
open BstLean.Part268 (cell12807)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12807 (gMinus 12807) (1 - (cell12807 i).lower) ≤ 1 ∧
    energyUpper 12807 (gMinus 12807) (BstLean.Part211.gPlus 12807)
      (finiteEnergy 12807 12807 0.011) (1 - (cell12807 i).lower) ≤
      (cell12807 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨10,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨11,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨12,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨13,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨14,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨15,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨16,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨17,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨18,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨19,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨20,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨21,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨22,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨23,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨24,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨25,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨26,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨27,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨28,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨29,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨30,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨31,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨32,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨33,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨34,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨35,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨36,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨37,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨38,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨39,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨40,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨41,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨42,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨43,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨44,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨45,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨46,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨47,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨48,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨49,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨50,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨51,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12807) (by norm_num)
        (q := 1 - (cell12807 ⟨52,by decide⟩).lower)
        (by norm_num [cell12807]) (by norm_num [cell12807])
      exact ⟨E.1,E.2.trans (by norm_num [cell12807])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12807

/-! Source-cell containment and simple scalar guards at 12807. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12807)
open BstLean.Part268 (cell12807)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12807 ⟨10,by decide⟩).lower ∧ (cell12807 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12807 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12807 ⟨11,by decide⟩).lower ∧ (cell12807 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12807 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12807 ⟨12,by decide⟩).lower ∧ (cell12807 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12807 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12807 ⟨13,by decide⟩).lower ∧ (cell12807 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12807 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12807 ⟨14,by decide⟩).lower ∧ (cell12807 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12807 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12807 ⟨15,by decide⟩).lower ∧ (cell12807 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12807 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12807 ⟨16,by decide⟩).lower ∧ (cell12807 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12807 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12807 ⟨17,by decide⟩).lower ∧ (cell12807 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12807 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12807 ⟨18,by decide⟩).lower ∧ (cell12807 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12807 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12807 ⟨19,by decide⟩).lower ∧ (cell12807 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12807 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12807 ⟨20,by decide⟩).lower ∧ (cell12807 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12807 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12807 ⟨21,by decide⟩).lower ∧ (cell12807 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12807 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12807 ⟨22,by decide⟩).lower ∧ (cell12807 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12807 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12807 ⟨23,by decide⟩).lower ∧ (cell12807 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12807 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12807 ⟨24,by decide⟩).lower ∧ (cell12807 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12807 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12807 ⟨25,by decide⟩).lower ∧ (cell12807 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12807 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12807 ⟨26,by decide⟩).lower ∧ (cell12807 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12807 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12807 ⟨27,by decide⟩).lower ∧ (cell12807 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12807 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12807 ⟨28,by decide⟩).lower ∧ (cell12807 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12807 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12807 ⟨29,by decide⟩).lower ∧ (cell12807 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12807 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12807 ⟨30,by decide⟩).lower ∧ (cell12807 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12807 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12807 ⟨31,by decide⟩).lower ∧ (cell12807 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12807 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12807 ⟨32,by decide⟩).lower ∧ (cell12807 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12807 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12807 ⟨33,by decide⟩).lower ∧ (cell12807 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12807 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12807 ⟨34,by decide⟩).lower ∧ (cell12807 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12807 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12807 ⟨35,by decide⟩).lower ∧ (cell12807 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12807 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12807 ⟨36,by decide⟩).lower ∧ (cell12807 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12807 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12807 ⟨37,by decide⟩).lower ∧ (cell12807 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12807 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12807 ⟨38,by decide⟩).lower ∧ (cell12807 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12807 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12807 ⟨39,by decide⟩).lower ∧ (cell12807 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12807 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12807 ⟨40,by decide⟩).lower ∧ (cell12807 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12807 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12807 ⟨41,by decide⟩).lower ∧ (cell12807 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12807 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12807 ⟨42,by decide⟩).lower ∧ (cell12807 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12807 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12807 ⟨43,by decide⟩).lower ∧ (cell12807 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12807 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12807 ⟨44,by decide⟩).lower ∧ (cell12807 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12807 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12807 ⟨45,by decide⟩).lower ∧ (cell12807 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12807 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12807 ⟨46,by decide⟩).lower ∧ (cell12807 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12807 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12807 ⟨47,by decide⟩).lower ∧ (cell12807 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12807 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12807 ⟨48,by decide⟩).lower ∧ (cell12807 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12807 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12807 ⟨49,by decide⟩).lower ∧ (cell12807 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12807 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12807 ⟨50,by decide⟩).lower ∧ (cell12807 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12807 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12807 ⟨51,by decide⟩).lower ∧ (cell12807 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12807 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12807 ⟨52,by decide⟩).lower ∧ (cell12807 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12807 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12807 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12807 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12807,cell12807,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12807 i).lower ∧
    (cell12807 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12807 i).upper ≤ (0.532 : ℝ) ∧
    (cell12807 i).centre ≤ (0.1 : ℝ) ∧ (cell12807 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12807 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12807 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12807

/-! The local source numeric instances at 12807 have no network premises. -/
namespace BstLean.Part269.N12807
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12807)
open BstLean.Part268 (cell12807)

noncomputable def sourceNumerics12807 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12807 (cell12807 i)
      scalarRow12807.M scalarRow12807.H scalarRow12807.xi := by
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
    energy_allowance := scalarRow12807.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12807]
    centre_nonneg := (scalarRow12807.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12807])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12807
/-! Actual 12808 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12808 ≤ (1.035656600502 : ℝ) := by
  have hr : (113.172434806360 : ℝ) ≤ √(12808 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.172434806360 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12808 12808 (11 / 1000) ≤
    (0.008446288178 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12808) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.172434806360 : ℝ) ≤ √(12808 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12808)
  have hdiv : K / √(12808 : ℝ) ≤ K / 113.172434806360 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.172434806360 ≤ (0.008446288178 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12808.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12808 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12808 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12808 := gPlus_lower 12808
end BstLean.Part269.N12808

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12808
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035656600501 : ℝ) ≤ wn 12808 := by
  have hn : √(12808 : ℝ) ≤ 113.172434806361 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12808 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.172434806361 ≤ 2 / √(12808 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249720151 : ℝ) ≤ rhoBar 12808 BstLean.Part154.csC ∧
    rhoBar 12808 BstLean.Part154.csC ≤ 0.000249720538 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035656600501 : ℝ) / (1.295212 * 12808) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035656600502 : ℝ) / (1.29521 * 12808) := by gcongr
      _ ≤ (0.000249720538 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12808 BstLean.Part154.csC) ≤ 0.000998944513 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12808 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) ≤ 0.000190738155 ∧
    cc1 (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) ≤ 0.000121367971 ∧
    cc2 (rhoBar 12808 BstLean.Part154.csC) ≤ 0.000070455056 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12808 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12808 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12808 BstLean.Part154.csC * nuR (rhoBar 12808 BstLean.Part154.csC)) ≤ 0.000499456667 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249720538 : ℝ) * 0.000998944513 := by gcongr
      _ ≤ (0.000499456667 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12808 BstLean.Part154.csC) * nuR (rhoBar 12808 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998944513 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12808 BstLean.Part154.csC) * rhoBar 12808 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249720538 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249720538 / 2 + 0.399 * 0.000998944513 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190738155 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499456667 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121367971 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249720538 / 1.414213562 := by gcongr
      _ ≤ (0.000070455056 : ℝ) := by norm_num

end BstLean.Part269.N12808

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12808
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) ≤ 1.57113E-7 := by
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12808 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12808 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12808 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190738155 : ℝ) ^ 2 + 0.000121367971 ^ 2 + 3 * 0.000070455056 ^ 2 +
        2 * 0.797885 * 0.000190738155 * 0.000121367971 + 2 * 0.000190738155 * 0.000070455056 +
        4 * 0.797885 * 0.000121367971 * 0.000070455056 := by gcongr
    _ ≤ (1.57113E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12808 BstLean.Part154.csC Θ ≤ 0.002606359396 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12808 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12808 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12808 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035656600502 * 1.57113E-7 / (0.000249720151 : ℝ) := by gcongr
    _ ≤ 0.002606359396 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12808 BstLean.Part154.csC Θ ≤ 0.002891458290 + 0.000658582588 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12808 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12808 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035656600502 : ℝ) * ((2 * Θ * 0.000249720538 +
        (6863 / 10000) * 0.000249720538 * 12808 * 0.000998944513) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002891458290 + 0.000658582588 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12808 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12808 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12808 0.011 Θ ∧ gammaRatio 12808 0.011 Θ ≤ 0.000085847464 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12808 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035656600502 : ℝ) * 0.525 / ((1 - 0.011) * 12808) := by gcongr
      _ ≤ (0.000085847464 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12808 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12808 0.011 Θ) :=
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
    badAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12808 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12808 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12808 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12808 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12808 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12808 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12808 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12808 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12808 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12808 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035656600502 : ℝ) * 12808 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003400262790 + 0.003264941984 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12808

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12808
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12808 BstLean.Part154.csC) (piBar (rhoBar 12808 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12808 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12808 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12808 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12808 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12808 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12808 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12808 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12808 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12808 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12808 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052260170092 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12808) ≤ 0.010552371548 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12808 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035656600502)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010552371548 + 2 * 0.737676 / 12808) := by gcongr
    _ ≤ (0.052260170092 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12808 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12808

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12808
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508411188 : ℝ) ≤ plow 12808 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12808) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620957332)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368338683) : eMP 12808 0.011 xi bn ≤ 0.001178149950 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12808 : ℝ) * (1 - 0.011))) ≤ 0.000582549666 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368338683 / (12808 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582549666 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582549666 : ℝ) + 3.141593 * 0.052620957332 / (12808 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178149950 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620957332)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368338683) : PiBarMP 12808 12 0.011 xi bn ≤ 0.160562787505 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12808 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036991062205 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.548265202090 : ℝ) ≤ √((12808 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.172434806360 : ℝ) ≤ √(12808 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12808) ≤ 0.123107789336 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036991062205 + 0.052620957332 * 1.772454 / (2 * (112.548265202090 : ℝ))) * (1 + 0.001178149950) +
        8 / (12808 * 113.172434806360) + 0.123107789336 := by gcongr
    _ ≤ (0.160562787505 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620957332)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368338683) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281652753521) :
    parallelOracle 12808 0.011 xi bn cd ≤ 0.161544524628 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12808 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12808 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508411188 : ℝ) ≤ plow 12808 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.172434806360 : ℝ) ≤ √(12808 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281652753521 : ℝ) / (2 * 0.560508411188 * 113.172434806360)) * 0.160562787505 +
        0.281652753521 ^ 2 / (2 * 0.560508411188 * 113.172434806360) := by gcongr
    _ ≤ (0.161544524628 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620957332) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368338683)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281652753521) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12808 12808 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508411188 : ℝ) ≤ plow 12808 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.172434806360 : ℝ) ≤ √(12808 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12808 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12808 Θ 1.22 ≤ 0.011717522048 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.172434806360 := by gcongr <;> linarith
      _ ≤ (0.011717522048 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12808 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12808 12808 0.011 ≤ 0.008446288178 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12808 12808 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12808 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12808 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12808 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12808 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161544524628 + 0.011717522048 + (0.008446288178 : ℝ) *
        (1 + 2 * (0.281652753521 + 0.011717522048) / (0.560508411188 * 113.172434806360))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12808]

end BstLean.Part269.N12808

/-! The original eight local profiles supply actual 12808 moment certificates. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12808 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052620957332 ∧
    0 ≤ bN 12808 BstLean.Part154.csC (groupTheta g) ∧ bN 12808 BstLean.Part154.csC (groupTheta g) ≤ 0.001368338683 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12808 12808 0.011
      (momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12808 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12808 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12808 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229392583429 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12808 0.011
      (momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12808 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12808
/-! The actual computed-centre upper energy formula at 12808. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12808

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12808)
open BstLean.Part268 (cell12808)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085181395248
  | 2 => 0.086118605806
  | 3 => 0.087053170106
  | 4 => 0.087986323645
  | 5 => 0.088919566596
  | 6 => 0.089854703853
  | 7 => 0.090793888988
  | 8 => 0.091739672179
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12808 12808 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12808 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12808

/-! Actual upper energy certificates on all 43 source endpoints at 12808. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12808)
open BstLean.Part268 (cell12808)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12808 (gMinus 12808) (1 - (cell12808 i).lower) ≤ 1 ∧
    energyUpper 12808 (gMinus 12808) (BstLean.Part211.gPlus 12808)
      (finiteEnergy 12808 12808 0.011) (1 - (cell12808 i).lower) ≤
      (cell12808 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨10,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨11,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨12,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨13,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨14,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨15,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨16,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨17,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨18,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨19,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨20,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨21,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨22,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨23,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨24,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨25,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨26,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨27,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨28,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨29,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨30,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨31,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨32,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨33,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨34,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨35,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨36,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨37,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨38,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨39,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨40,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨41,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨42,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨43,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨44,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨45,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨46,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨47,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨48,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨49,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨50,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨51,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12808) (by norm_num)
        (q := 1 - (cell12808 ⟨52,by decide⟩).lower)
        (by norm_num [cell12808]) (by norm_num [cell12808])
      exact ⟨E.1,E.2.trans (by norm_num [cell12808])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12808

/-! Source-cell containment and simple scalar guards at 12808. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12808)
open BstLean.Part268 (cell12808)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12808 ⟨10,by decide⟩).lower ∧ (cell12808 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12808 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12808 ⟨11,by decide⟩).lower ∧ (cell12808 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12808 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12808 ⟨12,by decide⟩).lower ∧ (cell12808 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12808 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12808 ⟨13,by decide⟩).lower ∧ (cell12808 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12808 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12808 ⟨14,by decide⟩).lower ∧ (cell12808 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12808 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12808 ⟨15,by decide⟩).lower ∧ (cell12808 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12808 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12808 ⟨16,by decide⟩).lower ∧ (cell12808 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12808 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12808 ⟨17,by decide⟩).lower ∧ (cell12808 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12808 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12808 ⟨18,by decide⟩).lower ∧ (cell12808 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12808 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12808 ⟨19,by decide⟩).lower ∧ (cell12808 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12808 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12808 ⟨20,by decide⟩).lower ∧ (cell12808 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12808 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12808 ⟨21,by decide⟩).lower ∧ (cell12808 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12808 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12808 ⟨22,by decide⟩).lower ∧ (cell12808 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12808 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12808 ⟨23,by decide⟩).lower ∧ (cell12808 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12808 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12808 ⟨24,by decide⟩).lower ∧ (cell12808 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12808 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12808 ⟨25,by decide⟩).lower ∧ (cell12808 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12808 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12808 ⟨26,by decide⟩).lower ∧ (cell12808 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12808 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12808 ⟨27,by decide⟩).lower ∧ (cell12808 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12808 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12808 ⟨28,by decide⟩).lower ∧ (cell12808 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12808 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12808 ⟨29,by decide⟩).lower ∧ (cell12808 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12808 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12808 ⟨30,by decide⟩).lower ∧ (cell12808 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12808 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12808 ⟨31,by decide⟩).lower ∧ (cell12808 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12808 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12808 ⟨32,by decide⟩).lower ∧ (cell12808 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12808 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12808 ⟨33,by decide⟩).lower ∧ (cell12808 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12808 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12808 ⟨34,by decide⟩).lower ∧ (cell12808 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12808 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12808 ⟨35,by decide⟩).lower ∧ (cell12808 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12808 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12808 ⟨36,by decide⟩).lower ∧ (cell12808 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12808 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12808 ⟨37,by decide⟩).lower ∧ (cell12808 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12808 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12808 ⟨38,by decide⟩).lower ∧ (cell12808 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12808 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12808 ⟨39,by decide⟩).lower ∧ (cell12808 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12808 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12808 ⟨40,by decide⟩).lower ∧ (cell12808 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12808 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12808 ⟨41,by decide⟩).lower ∧ (cell12808 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12808 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12808 ⟨42,by decide⟩).lower ∧ (cell12808 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12808 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12808 ⟨43,by decide⟩).lower ∧ (cell12808 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12808 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12808 ⟨44,by decide⟩).lower ∧ (cell12808 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12808 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12808 ⟨45,by decide⟩).lower ∧ (cell12808 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12808 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12808 ⟨46,by decide⟩).lower ∧ (cell12808 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12808 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12808 ⟨47,by decide⟩).lower ∧ (cell12808 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12808 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12808 ⟨48,by decide⟩).lower ∧ (cell12808 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12808 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12808 ⟨49,by decide⟩).lower ∧ (cell12808 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12808 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12808 ⟨50,by decide⟩).lower ∧ (cell12808 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12808 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12808 ⟨51,by decide⟩).lower ∧ (cell12808 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12808 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12808 ⟨52,by decide⟩).lower ∧ (cell12808 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12808 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12808 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12808 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12808,cell12808,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12808 i).lower ∧
    (cell12808 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12808 i).upper ≤ (0.532 : ℝ) ∧
    (cell12808 i).centre ≤ (0.1 : ℝ) ∧ (cell12808 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12808 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12808 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12808

/-! The local source numeric instances at 12808 have no network premises. -/
namespace BstLean.Part269.N12808
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12808)
open BstLean.Part268 (cell12808)

noncomputable def sourceNumerics12808 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12808 (cell12808 i)
      scalarRow12808.M scalarRow12808.H scalarRow12808.xi := by
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
    energy_allowance := scalarRow12808.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12808]
    centre_nonneg := (scalarRow12808.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12808])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12808
/-! Actual 12809 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12809 ≤ (1.035655196427 : ℝ) := by
  have hr : (113.176852757089 : ℝ) ≤ √(12809 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.176852757089 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12809 12809 (11 / 1000) ≤
    (0.008445958467 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12809) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.176852757089 : ℝ) ≤ √(12809 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12809)
  have hdiv : K / √(12809 : ℝ) ≤ K / 113.176852757089 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.176852757089 ≤ (0.008445958467 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12809.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12809 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12809 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12809 := gPlus_lower 12809
end BstLean.Part269.N12809

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12809
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035655196426 : ℝ) ≤ wn 12809 := by
  have hn : √(12809 : ℝ) ≤ 113.176852757090 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12809 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.176852757090 ≤ 2 / √(12809 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249700317 : ℝ) ≤ rhoBar 12809 BstLean.Part154.csC ∧
    rhoBar 12809 BstLean.Part154.csC ≤ 0.000249700704 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035655196426 : ℝ) / (1.295212 * 12809) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035655196427 : ℝ) / (1.29521 * 12809) := by gcongr
      _ ≤ (0.000249700704 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12809 BstLean.Part154.csC) ≤ 0.000998865167 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12809 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) ≤ 0.000190723005 ∧
    cc1 (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) ≤ 0.000121358331 ∧
    cc2 (rhoBar 12809 BstLean.Part154.csC) ≤ 0.000070449460 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12809 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12809 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12809 BstLean.Part154.csC * nuR (rhoBar 12809 BstLean.Part154.csC)) ≤ 0.000499416996 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249700704 : ℝ) * 0.000998865167 := by gcongr
      _ ≤ (0.000499416996 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12809 BstLean.Part154.csC) * nuR (rhoBar 12809 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998865167 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12809 BstLean.Part154.csC) * rhoBar 12809 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249700704 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249700704 / 2 + 0.399 * 0.000998865167 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190723005 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499416996 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121358331 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249700704 / 1.414213562 := by gcongr
      _ ≤ (0.000070449460 : ℝ) := by norm_num

end BstLean.Part269.N12809

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12809
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) ≤ 1.57088E-7 := by
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12809 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12809 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12809 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190723005 : ℝ) ^ 2 + 0.000121358331 ^ 2 + 3 * 0.000070449460 ^ 2 +
        2 * 0.797885 * 0.000190723005 * 0.000121358331 + 2 * 0.000190723005 * 0.000070449460 +
        4 * 0.797885 * 0.000121358331 * 0.000070449460 := by gcongr
    _ ≤ (1.57088E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12809 BstLean.Part154.csC Θ ≤ 0.002606148130 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12809 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12809 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12809 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035655196427 * 1.57088E-7 / (0.000249700317 : ℝ) := by gcongr
    _ ≤ 0.002606148130 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12809 BstLean.Part154.csC Θ ≤ 0.002891220785 + 0.000658529387 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12809 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12809 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035655196427 : ℝ) * ((2 * Θ * 0.000249700704 +
        (6863 / 10000) * 0.000249700704 * 12809 * 0.000998865167) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002891220785 + 0.000658529387 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12809 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12809 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12809 0.011 Θ ∧ gammaRatio 12809 0.011 Θ ≤ 0.000085840645 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12809 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035655196427 : ℝ) * 0.525 / ((1 - 0.011) * 12809) := by gcongr
      _ ≤ (0.000085840645 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12809 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12809 0.011 Θ) :=
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
    badAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12809 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12809 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12809 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12809 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12809 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12809 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12809 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12809 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12809 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12809 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035655196427 : ℝ) * 12809 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003400025285 + 0.003264677517 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12809

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12809
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12809 BstLean.Part154.csC) (piBar (rhoBar 12809 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12809 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12809 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12809 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12809 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12809 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12809 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12809 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12809 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12809 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12809 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052258108048 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12809) ≤ 0.010551959628 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12809 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035655196427)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010551959628 + 2 * 0.737676 / 12809) := by gcongr
    _ ≤ (0.052258108048 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12809 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12809

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12809
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508455648 : ℝ) ≤ plow 12809 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12809) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620580982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368227769) : eMP 12809 0.011 xi bn ≤ 0.001178056138 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12809 : ℝ) * (1 - 0.011))) ≤ 0.000582503316 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368227769 / (12809 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582503316 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582503316 : ℝ) + 3.141593 * 0.052620580982 / (12809 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001178056138 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620580982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368227769) : PiBarMP 12809 12 0.011 xi bn ≤ 0.160556457579 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12809 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036989562974 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.552658786898 : ℝ) ≤ √((12809 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.176852757089 : ℝ) ≤ √(12809 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12809) ≤ 0.123102983723 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036989562974 + 0.052620580982 * 1.772454 / (2 * (112.552658786898 : ℝ))) * (1 + 0.001178056138) +
        8 / (12809 * 113.176852757089) + 0.123102983723 := by gcongr
    _ ≤ (0.160556457579 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620580982)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368227769) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281649871157) :
    parallelOracle 12809 0.011 xi bn cd ≤ 0.161538125804 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12809 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12809 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508455648 : ℝ) ≤ plow 12809 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.176852757089 : ℝ) ≤ √(12809 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281649871157 : ℝ) / (2 * 0.560508455648 * 113.176852757089)) * 0.160556457579 +
        0.281649871157 ^ 2 / (2 * 0.560508455648 * 113.176852757089) := by gcongr
    _ ≤ (0.161538125804 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620580982) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368227769)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281649871157) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12809 12809 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508455648 : ℝ) ≤ plow 12809 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.176852757089 : ℝ) ≤ √(12809 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12809 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12809 Θ 1.22 ≤ 0.011717064645 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.176852757089 := by gcongr <;> linarith
      _ ≤ (0.011717064645 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12809 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12809 12809 0.011 ≤ 0.008445958467 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12809 12809 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12809 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12809 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12809 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12809 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161538125804 + 0.011717064645 + (0.008445958467 : ℝ) *
        (1 + 2 * (0.281649871157 + 0.011717064645) / (0.560508455648 * 113.176852757089))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12809]

end BstLean.Part269.N12809

/-! The original eight local profiles supply actual 12809 moment certificates. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12809 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052620580982 ∧
    0 ≤ bN 12809 BstLean.Part154.csC (groupTheta g) ∧ bN 12809 BstLean.Part154.csC (groupTheta g) ≤ 0.001368227769 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12809 12809 0.011
      (momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12809 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12809 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12809 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229391763109 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12809 0.011
      (momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12809 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12809
/-! The actual computed-centre upper energy formula at 12809. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12809

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12809)
open BstLean.Part268 (cell12809)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085178590389
  | 2 => 0.086115751872
  | 3 => 0.087050260340
  | 4 => 0.087983349707
  | 5 => 0.088916518276
  | 6 => 0.089851568754
  | 7 => 0.090790652166
  | 8 => 0.091736315743
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12809 12809 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12809 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12809

/-! Actual upper energy certificates on all 43 source endpoints at 12809. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12809)
open BstLean.Part268 (cell12809)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12809 (gMinus 12809) (1 - (cell12809 i).lower) ≤ 1 ∧
    energyUpper 12809 (gMinus 12809) (BstLean.Part211.gPlus 12809)
      (finiteEnergy 12809 12809 0.011) (1 - (cell12809 i).lower) ≤
      (cell12809 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨10,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨11,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨12,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨13,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨14,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨15,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨16,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨17,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨18,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨19,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨20,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨21,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨22,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨23,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨24,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨25,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨26,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨27,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨28,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨29,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨30,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨31,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨32,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨33,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨34,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨35,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨36,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨37,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨38,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨39,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨40,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨41,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨42,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨43,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨44,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨45,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨46,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨47,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨48,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨49,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨50,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨51,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12809) (by norm_num)
        (q := 1 - (cell12809 ⟨52,by decide⟩).lower)
        (by norm_num [cell12809]) (by norm_num [cell12809])
      exact ⟨E.1,E.2.trans (by norm_num [cell12809])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12809

/-! Source-cell containment and simple scalar guards at 12809. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12809)
open BstLean.Part268 (cell12809)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12809 ⟨10,by decide⟩).lower ∧ (cell12809 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12809 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12809 ⟨11,by decide⟩).lower ∧ (cell12809 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12809 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12809 ⟨12,by decide⟩).lower ∧ (cell12809 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12809 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12809 ⟨13,by decide⟩).lower ∧ (cell12809 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12809 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12809 ⟨14,by decide⟩).lower ∧ (cell12809 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12809 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12809 ⟨15,by decide⟩).lower ∧ (cell12809 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12809 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12809 ⟨16,by decide⟩).lower ∧ (cell12809 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12809 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12809 ⟨17,by decide⟩).lower ∧ (cell12809 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12809 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12809 ⟨18,by decide⟩).lower ∧ (cell12809 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12809 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12809 ⟨19,by decide⟩).lower ∧ (cell12809 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12809 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12809 ⟨20,by decide⟩).lower ∧ (cell12809 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12809 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12809 ⟨21,by decide⟩).lower ∧ (cell12809 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12809 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12809 ⟨22,by decide⟩).lower ∧ (cell12809 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12809 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12809 ⟨23,by decide⟩).lower ∧ (cell12809 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12809 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12809 ⟨24,by decide⟩).lower ∧ (cell12809 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12809 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12809 ⟨25,by decide⟩).lower ∧ (cell12809 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12809 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12809 ⟨26,by decide⟩).lower ∧ (cell12809 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12809 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12809 ⟨27,by decide⟩).lower ∧ (cell12809 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12809 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12809 ⟨28,by decide⟩).lower ∧ (cell12809 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12809 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12809 ⟨29,by decide⟩).lower ∧ (cell12809 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12809 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12809 ⟨30,by decide⟩).lower ∧ (cell12809 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12809 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12809 ⟨31,by decide⟩).lower ∧ (cell12809 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12809 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12809 ⟨32,by decide⟩).lower ∧ (cell12809 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12809 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12809 ⟨33,by decide⟩).lower ∧ (cell12809 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12809 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12809 ⟨34,by decide⟩).lower ∧ (cell12809 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12809 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12809 ⟨35,by decide⟩).lower ∧ (cell12809 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12809 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12809 ⟨36,by decide⟩).lower ∧ (cell12809 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12809 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12809 ⟨37,by decide⟩).lower ∧ (cell12809 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12809 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12809 ⟨38,by decide⟩).lower ∧ (cell12809 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12809 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12809 ⟨39,by decide⟩).lower ∧ (cell12809 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12809 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12809 ⟨40,by decide⟩).lower ∧ (cell12809 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12809 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12809 ⟨41,by decide⟩).lower ∧ (cell12809 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12809 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12809 ⟨42,by decide⟩).lower ∧ (cell12809 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12809 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12809 ⟨43,by decide⟩).lower ∧ (cell12809 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12809 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12809 ⟨44,by decide⟩).lower ∧ (cell12809 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12809 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12809 ⟨45,by decide⟩).lower ∧ (cell12809 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12809 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12809 ⟨46,by decide⟩).lower ∧ (cell12809 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12809 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12809 ⟨47,by decide⟩).lower ∧ (cell12809 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12809 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12809 ⟨48,by decide⟩).lower ∧ (cell12809 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12809 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12809 ⟨49,by decide⟩).lower ∧ (cell12809 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12809 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12809 ⟨50,by decide⟩).lower ∧ (cell12809 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12809 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12809 ⟨51,by decide⟩).lower ∧ (cell12809 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12809 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12809 ⟨52,by decide⟩).lower ∧ (cell12809 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12809 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12809 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12809 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12809,cell12809,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12809 i).lower ∧
    (cell12809 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12809 i).upper ≤ (0.532 : ℝ) ∧
    (cell12809 i).centre ≤ (0.1 : ℝ) ∧ (cell12809 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12809 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12809 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12809

/-! The local source numeric instances at 12809 have no network premises. -/
namespace BstLean.Part269.N12809
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12809)
open BstLean.Part268 (cell12809)

noncomputable def sourceNumerics12809 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12809 (cell12809 i)
      scalarRow12809.M scalarRow12809.H scalarRow12809.xi := by
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
    energy_allowance := scalarRow12809.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12809]
    centre_nonneg := (scalarRow12809.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12809])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12809
/-! Actual 12810 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12810 ≤ (1.035653792517 : ℝ) := by
  have hr : (113.181270535367 : ℝ) ≤ √(12810 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.181270535367 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12810 12810 (11 / 1000) ≤
    (0.008445628796 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12810) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.181270535367 : ℝ) ≤ √(12810 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12810)
  have hdiv : K / √(12810 : ℝ) ≤ K / 113.181270535367 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.181270535367 ≤ (0.008445628796 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12810.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12810 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12810 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12810 := gPlus_lower 12810
end BstLean.Part269.N12810

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12810
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035653792516 : ℝ) ≤ wn 12810 := by
  have hn : √(12810 : ℝ) ≤ 113.181270535368 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12810 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.181270535368 ≤ 2 / √(12810 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249680486 : ℝ) ≤ rhoBar 12810 BstLean.Part154.csC ∧
    rhoBar 12810 BstLean.Part154.csC ≤ 0.000249680873 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035653792516 : ℝ) / (1.295212 * 12810) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035653792517 : ℝ) / (1.29521 * 12810) := by gcongr
      _ ≤ (0.000249680873 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12810 BstLean.Part154.csC) ≤ 0.000998785833 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12810 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) ≤ 0.000190707858 ∧
    cc1 (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) ≤ 0.000121348692 ∧
    cc2 (rhoBar 12810 BstLean.Part154.csC) ≤ 0.000070443865 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12810 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12810 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12810 BstLean.Part154.csC * nuR (rhoBar 12810 BstLean.Part154.csC)) ≤ 0.000499377332 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249680873 : ℝ) * 0.000998785833 := by gcongr
      _ ≤ (0.000499377332 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12810 BstLean.Part154.csC) * nuR (rhoBar 12810 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998785833 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12810 BstLean.Part154.csC) * rhoBar 12810 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249680873 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249680873 / 2 + 0.399 * 0.000998785833 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190707858 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499377332 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121348692 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249680873 / 1.414213562 := by gcongr
      _ ≤ (0.000070443865 : ℝ) := by norm_num

end BstLean.Part269.N12810

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12810
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) ≤ 1.57063E-7 := by
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12810 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12810 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12810 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190707858 : ℝ) ^ 2 + 0.000121348692 ^ 2 + 3 * 0.000070443865 ^ 2 +
        2 * 0.797885 * 0.000190707858 * 0.000121348692 + 2 * 0.000190707858 * 0.000070443865 +
        4 * 0.797885 * 0.000121348692 * 0.000070443865 := by gcongr
    _ ≤ (1.57063E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12810 BstLean.Part154.csC Θ ≤ 0.002605936799 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12810 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12810 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12810 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035653792517 * 1.57063E-7 / (0.000249680486 : ℝ) := by gcongr
    _ ≤ 0.002605936799 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12810 BstLean.Part154.csC Θ ≤ 0.002890983316 + 0.000658476195 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12810 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12810 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035653792517 : ℝ) * ((2 * Θ * 0.000249680873 +
        (6863 / 10000) * 0.000249680873 * 12810 * 0.000998785833) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002890983316 + 0.000658476195 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12810 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12810 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12810 0.011 Θ ∧ gammaRatio 12810 0.011 Θ ≤ 0.000085833828 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12810 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035653792517 : ℝ) * 0.525 / ((1 - 0.011) * 12810) := by gcongr
      _ ≤ (0.000085833828 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12810 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12810 0.011 Θ) :=
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
    badAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12810 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12810 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12810 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12810 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12810 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12810 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12810 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12810 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12810 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12810 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035653792517 : ℝ) * 12810 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003399787816 + 0.003264412994 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12810

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12810
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12810 BstLean.Part154.csC) (piBar (rhoBar 12810 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12810 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12810 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12810 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12810 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12810 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12810 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12810 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12810 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12810 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12810 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052256046246 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12810) ≤ 0.010551547756 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12810 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035653792517)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010551547756 + 2 * 0.737676 / 12810) := by gcongr
    _ ≤ (0.052256046246 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12810 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12810

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12810
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508500101 : ℝ) ≤ plow 12810 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12810) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620204638)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368116820) : eMP 12810 0.011 xi bn ≤ 0.001177962320 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12810 : ℝ) * (1 - 0.011))) ≤ 0.000582456963 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368116820 / (12810 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582456963 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582456963 : ℝ) + 3.141593 * 0.052620204638 / (12810 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177962320 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620204638)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368116820) : PiBarMP 12810 12 0.011 xi bn ≤ 0.160550127685 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12810 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036988063210 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.557052200206 : ℝ) ≤ √((12810 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.181270535367 : ℝ) ≤ √(12810 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12810) ≤ 0.123098178673 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036988063210 + 0.052620204638 * 1.772454 / (2 * (112.557052200206 : ℝ))) * (1 + 0.001177962320) +
        8 / (12810 * 113.181270535367) + 0.123098178673 := by gcongr
    _ ≤ (0.160550127685 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620204638)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368116820) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281646989045) :
    parallelOracle 12810 0.011 xi bn cd ≤ 0.161531727021 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12810 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12810 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508500101 : ℝ) ≤ plow 12810 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.181270535367 : ℝ) ≤ √(12810 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281646989045 : ℝ) / (2 * 0.560508500101 * 113.181270535367)) * 0.160550127685 +
        0.281646989045 ^ 2 / (2 * 0.560508500101 * 113.181270535367) := by gcongr
    _ ≤ (0.161531727021 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052620204638) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368116820)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281646989045) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12810 12810 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508500101 : ℝ) ≤ plow 12810 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.181270535367 : ℝ) ≤ √(12810 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12810 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12810 Θ 1.22 ≤ 0.011716607295 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.181270535367 := by gcongr <;> linarith
      _ ≤ (0.011716607295 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12810 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12810 12810 0.011 ≤ 0.008445628796 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12810 12810 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12810 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12810 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12810 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12810 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161531727021 + 0.011716607295 + (0.008445628796 : ℝ) *
        (1 + 2 * (0.281646989045 + 0.011716607295) / (0.560508500101 * 113.181270535367))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12810]

end BstLean.Part269.N12810

/-! The original eight local profiles supply actual 12810 moment certificates. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12810 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052620204638 ∧
    0 ≤ bN 12810 BstLean.Part154.csC (groupTheta g) ∧ bN 12810 BstLean.Part154.csC (groupTheta g) ≤ 0.001368116820 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12810 12810 0.011
      (momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12810 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12810 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12810 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229390942799 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12810 0.011
      (momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12810 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12810
/-! The actual computed-centre upper energy formula at 12810. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12810

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12810)
open BstLean.Part268 (cell12810)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085175786503
  | 2 => 0.086112898950
  | 3 => 0.087047351633
  | 4 => 0.087980376886
  | 5 => 0.088913471145
  | 6 => 0.089848434932
  | 7 => 0.090787416726
  | 8 => 0.091732960816
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12810 12810 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12810 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12810

/-! Actual upper energy certificates on all 43 source endpoints at 12810. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12810)
open BstLean.Part268 (cell12810)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12810 (gMinus 12810) (1 - (cell12810 i).lower) ≤ 1 ∧
    energyUpper 12810 (gMinus 12810) (BstLean.Part211.gPlus 12810)
      (finiteEnergy 12810 12810 0.011) (1 - (cell12810 i).lower) ≤
      (cell12810 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨10,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨11,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨12,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨13,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨14,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨15,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨16,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨17,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨18,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨19,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨20,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨21,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨22,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨23,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨24,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨25,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨26,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨27,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨28,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨29,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨30,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨31,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨32,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨33,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨34,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨35,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨36,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨37,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨38,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨39,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨40,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨41,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨42,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨43,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨44,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨45,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨46,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨47,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨48,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨49,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨50,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨51,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12810) (by norm_num)
        (q := 1 - (cell12810 ⟨52,by decide⟩).lower)
        (by norm_num [cell12810]) (by norm_num [cell12810])
      exact ⟨E.1,E.2.trans (by norm_num [cell12810])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12810

/-! Source-cell containment and simple scalar guards at 12810. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12810)
open BstLean.Part268 (cell12810)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12810 ⟨10,by decide⟩).lower ∧ (cell12810 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12810 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12810 ⟨11,by decide⟩).lower ∧ (cell12810 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12810 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12810 ⟨12,by decide⟩).lower ∧ (cell12810 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12810 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12810 ⟨13,by decide⟩).lower ∧ (cell12810 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12810 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12810 ⟨14,by decide⟩).lower ∧ (cell12810 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12810 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12810 ⟨15,by decide⟩).lower ∧ (cell12810 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12810 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12810 ⟨16,by decide⟩).lower ∧ (cell12810 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12810 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12810 ⟨17,by decide⟩).lower ∧ (cell12810 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12810 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12810 ⟨18,by decide⟩).lower ∧ (cell12810 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12810 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12810 ⟨19,by decide⟩).lower ∧ (cell12810 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12810 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12810 ⟨20,by decide⟩).lower ∧ (cell12810 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12810 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12810 ⟨21,by decide⟩).lower ∧ (cell12810 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12810 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12810 ⟨22,by decide⟩).lower ∧ (cell12810 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12810 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12810 ⟨23,by decide⟩).lower ∧ (cell12810 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12810 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12810 ⟨24,by decide⟩).lower ∧ (cell12810 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12810 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12810 ⟨25,by decide⟩).lower ∧ (cell12810 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12810 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12810 ⟨26,by decide⟩).lower ∧ (cell12810 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12810 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12810 ⟨27,by decide⟩).lower ∧ (cell12810 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12810 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12810 ⟨28,by decide⟩).lower ∧ (cell12810 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12810 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12810 ⟨29,by decide⟩).lower ∧ (cell12810 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12810 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12810 ⟨30,by decide⟩).lower ∧ (cell12810 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12810 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12810 ⟨31,by decide⟩).lower ∧ (cell12810 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12810 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12810 ⟨32,by decide⟩).lower ∧ (cell12810 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12810 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12810 ⟨33,by decide⟩).lower ∧ (cell12810 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12810 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12810 ⟨34,by decide⟩).lower ∧ (cell12810 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12810 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12810 ⟨35,by decide⟩).lower ∧ (cell12810 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12810 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12810 ⟨36,by decide⟩).lower ∧ (cell12810 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12810 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12810 ⟨37,by decide⟩).lower ∧ (cell12810 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12810 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12810 ⟨38,by decide⟩).lower ∧ (cell12810 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12810 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12810 ⟨39,by decide⟩).lower ∧ (cell12810 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12810 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12810 ⟨40,by decide⟩).lower ∧ (cell12810 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12810 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12810 ⟨41,by decide⟩).lower ∧ (cell12810 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12810 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12810 ⟨42,by decide⟩).lower ∧ (cell12810 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12810 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12810 ⟨43,by decide⟩).lower ∧ (cell12810 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12810 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12810 ⟨44,by decide⟩).lower ∧ (cell12810 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12810 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12810 ⟨45,by decide⟩).lower ∧ (cell12810 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12810 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12810 ⟨46,by decide⟩).lower ∧ (cell12810 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12810 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12810 ⟨47,by decide⟩).lower ∧ (cell12810 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12810 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12810 ⟨48,by decide⟩).lower ∧ (cell12810 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12810 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12810 ⟨49,by decide⟩).lower ∧ (cell12810 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12810 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12810 ⟨50,by decide⟩).lower ∧ (cell12810 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12810 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12810 ⟨51,by decide⟩).lower ∧ (cell12810 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12810 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12810 ⟨52,by decide⟩).lower ∧ (cell12810 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12810 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12810 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12810 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12810,cell12810,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12810 i).lower ∧
    (cell12810 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12810 i).upper ≤ (0.532 : ℝ) ∧
    (cell12810 i).centre ≤ (0.1 : ℝ) ∧ (cell12810 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12810 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12810 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12810

/-! The local source numeric instances at 12810 have no network premises. -/
namespace BstLean.Part269.N12810
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12810)
open BstLean.Part268 (cell12810)

noncomputable def sourceNumerics12810 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12810 (cell12810 i)
      scalarRow12810.M scalarRow12810.H scalarRow12810.xi := by
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
    energy_allowance := scalarRow12810.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12810]
    centre_nonneg := (scalarRow12810.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12810])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12810
/-! Actual 12811 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12811 ≤ (1.035652388773 : ℝ) := by
  have hr : (113.185688141213 : ℝ) ≤ √(12811 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.185688141213 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12811 12811 (11 / 1000) ≤
    (0.008445299163 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12811) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.185688141213 : ℝ) ≤ √(12811 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12811)
  have hdiv : K / √(12811 : ℝ) ≤ K / 113.185688141213 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.185688141213 ≤ (0.008445299163 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12811.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12811 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12811 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12811 := gPlus_lower 12811
end BstLean.Part269.N12811

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12811
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035652388772 : ℝ) ≤ wn 12811 := by
  have hn : √(12811 : ℝ) ≤ 113.185688141214 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12811 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.185688141214 ≤ 2 / √(12811 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249660658 : ℝ) ≤ rhoBar 12811 BstLean.Part154.csC ∧
    rhoBar 12811 BstLean.Part154.csC ≤ 0.000249661045 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035652388772 : ℝ) / (1.295212 * 12811) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035652388773 : ℝ) / (1.29521 * 12811) := by gcongr
      _ ≤ (0.000249661045 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12811 BstLean.Part154.csC) ≤ 0.000998706511 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12811 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) ≤ 0.000190692712 ∧
    cc1 (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) ≤ 0.000121339055 ∧
    cc2 (rhoBar 12811 BstLean.Part154.csC) ≤ 0.000070438271 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12811 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12811 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12811 BstLean.Part154.csC * nuR (rhoBar 12811 BstLean.Part154.csC)) ≤ 0.000499337673 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249661045 : ℝ) * 0.000998706511 := by gcongr
      _ ≤ (0.000499337673 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12811 BstLean.Part154.csC) * nuR (rhoBar 12811 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998706511 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12811 BstLean.Part154.csC) * rhoBar 12811 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249661045 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249661045 / 2 + 0.399 * 0.000998706511 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190692712 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499337673 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121339055 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249661045 / 1.414213562 := by gcongr
      _ ≤ (0.000070438271 : ℝ) := by norm_num

end BstLean.Part269.N12811

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12811
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) ≤ 1.57038E-7 := by
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12811 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12811 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12811 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190692712 : ℝ) ^ 2 + 0.000121339055 ^ 2 + 3 * 0.000070438271 ^ 2 +
        2 * 0.797885 * 0.000190692712 * 0.000121339055 + 2 * 0.000190692712 * 0.000070438271 +
        4 * 0.797885 * 0.000121339055 * 0.000070438271 := by gcongr
    _ ≤ (1.57038E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12811 BstLean.Part154.csC Θ ≤ 0.002605725406 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12811 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12811 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12811 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035652388773 * 1.57038E-7 / (0.000249660658 : ℝ) := by gcongr
    _ ≤ 0.002605725406 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12811 BstLean.Part154.csC Θ ≤ 0.002890745882 + 0.000658423011 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12811 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12811 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035652388773 : ℝ) * ((2 * Θ * 0.000249661045 +
        (6863 / 10000) * 0.000249661045 * 12811 * 0.000998706511) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002890745882 + 0.000658423011 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12811 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12811 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12811 0.011 Θ ∧ gammaRatio 12811 0.011 Θ ≤ 0.000085827011 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12811 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035652388773 : ℝ) * 0.525 / ((1 - 0.011) * 12811) := by gcongr
      _ ≤ (0.000085827011 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12811 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12811 0.011 Θ) :=
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
    badAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12811 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12811 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12811 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12811 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12811 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12811 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12811 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12811 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12811 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12811 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035652388773 : ℝ) * 12811 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003399550382 + 0.003264148417 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12811

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12811
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12811 BstLean.Part154.csC) (piBar (rhoBar 12811 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12811 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12811 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12811 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12811 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12811 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12811 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12811 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12811 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12811 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12811 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052253984686 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12811) ≤ 0.010551135932 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12811 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035652388773)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010551135932 + 2 * 0.737676 / 12811) := by gcongr
    _ ≤ (0.052253984686 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12811 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12811

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12811
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508544547 : ℝ) ≤ plow 12811 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12811) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619828301)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368005839) : eMP 12811 0.011 xi bn ≤ 0.001177868494 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12811 : ℝ) * (1 - 0.011))) ≤ 0.000582410606 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001368005839 / (12811 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582410606 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582410606 : ℝ) + 3.141593 * 0.052619828301 / (12811 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177868494 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619828301)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368005839) : PiBarMP 12811 12 0.011 xi bn ≤ 0.160543797861 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12811 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036986562952 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.561445442034 : ℝ) ≤ √((12811 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.185688141213 : ℝ) ≤ √(12811 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12811) ≤ 0.123093374185 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036986562952 + 0.052619828301 * 1.772454 / (2 * (112.561445442034 : ℝ))) * (1 + 0.001177868494) +
        8 / (12811 * 113.185688141213) + 0.123093374185 := by gcongr
    _ ≤ (0.160543797861 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619828301)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368005839) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281644107187) :
    parallelOracle 12811 0.011 xi bn cd ≤ 0.161525328317 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12811 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12811 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508544547 : ℝ) ≤ plow 12811 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.185688141213 : ℝ) ≤ √(12811 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281644107187 : ℝ) / (2 * 0.560508544547 * 113.185688141213)) * 0.160543797861 +
        0.281644107187 ^ 2 / (2 * 0.560508544547 * 113.185688141213) := by gcongr
    _ ≤ (0.161525328317 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619828301) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001368005839)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281644107187) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12811 12811 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508544547 : ℝ) ≤ plow 12811 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.185688141213 : ℝ) ≤ √(12811 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12811 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12811 Θ 1.22 ≤ 0.011716149999 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.185688141213 := by gcongr <;> linarith
      _ ≤ (0.011716149999 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12811 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12811 12811 0.011 ≤ 0.008445299163 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12811 12811 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12811 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12811 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12811 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12811 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161525328317 + 0.011716149999 + (0.008445299163 : ℝ) *
        (1 + 2 * (0.281644107187 + 0.011716149999) / (0.560508544547 * 113.185688141213))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12811]

end BstLean.Part269.N12811

/-! The original eight local profiles supply actual 12811 moment certificates. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12811 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052619828301 ∧
    0 ≤ bN 12811 BstLean.Part154.csC (groupTheta g) ∧ bN 12811 BstLean.Part154.csC (groupTheta g) ≤ 0.001368005839 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12811 12811 0.011
      (momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12811 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12811 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12811 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229390122501 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12811 0.011
      (momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12811 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12811
/-! The actual computed-centre upper energy formula at 12811. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12811

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12811)
open BstLean.Part268 (cell12811)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085172983588
  | 2 => 0.086110047037
  | 3 => 0.087044443984
  | 4 => 0.087977405181
  | 5 => 0.088910425202
  | 6 => 0.089845302385
  | 7 => 0.090784182668
  | 8 => 0.091729607398
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12811 12811 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12811 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12811

/-! Actual upper energy certificates on all 43 source endpoints at 12811. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12811)
open BstLean.Part268 (cell12811)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12811 (gMinus 12811) (1 - (cell12811 i).lower) ≤ 1 ∧
    energyUpper 12811 (gMinus 12811) (BstLean.Part211.gPlus 12811)
      (finiteEnergy 12811 12811 0.011) (1 - (cell12811 i).lower) ≤
      (cell12811 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨10,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨11,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨12,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨13,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨14,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨15,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨16,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨17,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨18,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨19,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨20,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨21,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨22,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨23,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨24,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨25,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨26,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨27,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨28,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨29,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨30,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨31,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨32,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨33,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨34,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨35,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨36,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨37,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨38,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨39,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨40,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨41,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨42,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨43,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨44,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨45,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨46,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨47,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨48,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨49,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨50,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨51,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12811) (by norm_num)
        (q := 1 - (cell12811 ⟨52,by decide⟩).lower)
        (by norm_num [cell12811]) (by norm_num [cell12811])
      exact ⟨E.1,E.2.trans (by norm_num [cell12811])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12811

/-! Source-cell containment and simple scalar guards at 12811. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12811)
open BstLean.Part268 (cell12811)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12811 ⟨10,by decide⟩).lower ∧ (cell12811 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12811 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12811 ⟨11,by decide⟩).lower ∧ (cell12811 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12811 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12811 ⟨12,by decide⟩).lower ∧ (cell12811 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12811 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12811 ⟨13,by decide⟩).lower ∧ (cell12811 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12811 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12811 ⟨14,by decide⟩).lower ∧ (cell12811 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12811 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12811 ⟨15,by decide⟩).lower ∧ (cell12811 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12811 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12811 ⟨16,by decide⟩).lower ∧ (cell12811 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12811 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12811 ⟨17,by decide⟩).lower ∧ (cell12811 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12811 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12811 ⟨18,by decide⟩).lower ∧ (cell12811 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12811 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12811 ⟨19,by decide⟩).lower ∧ (cell12811 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12811 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12811 ⟨20,by decide⟩).lower ∧ (cell12811 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12811 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12811 ⟨21,by decide⟩).lower ∧ (cell12811 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12811 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12811 ⟨22,by decide⟩).lower ∧ (cell12811 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12811 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12811 ⟨23,by decide⟩).lower ∧ (cell12811 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12811 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12811 ⟨24,by decide⟩).lower ∧ (cell12811 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12811 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12811 ⟨25,by decide⟩).lower ∧ (cell12811 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12811 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12811 ⟨26,by decide⟩).lower ∧ (cell12811 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12811 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12811 ⟨27,by decide⟩).lower ∧ (cell12811 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12811 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12811 ⟨28,by decide⟩).lower ∧ (cell12811 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12811 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12811 ⟨29,by decide⟩).lower ∧ (cell12811 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12811 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12811 ⟨30,by decide⟩).lower ∧ (cell12811 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12811 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12811 ⟨31,by decide⟩).lower ∧ (cell12811 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12811 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12811 ⟨32,by decide⟩).lower ∧ (cell12811 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12811 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12811 ⟨33,by decide⟩).lower ∧ (cell12811 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12811 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12811 ⟨34,by decide⟩).lower ∧ (cell12811 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12811 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12811 ⟨35,by decide⟩).lower ∧ (cell12811 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12811 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12811 ⟨36,by decide⟩).lower ∧ (cell12811 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12811 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12811 ⟨37,by decide⟩).lower ∧ (cell12811 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12811 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12811 ⟨38,by decide⟩).lower ∧ (cell12811 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12811 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12811 ⟨39,by decide⟩).lower ∧ (cell12811 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12811 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12811 ⟨40,by decide⟩).lower ∧ (cell12811 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12811 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12811 ⟨41,by decide⟩).lower ∧ (cell12811 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12811 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12811 ⟨42,by decide⟩).lower ∧ (cell12811 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12811 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12811 ⟨43,by decide⟩).lower ∧ (cell12811 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12811 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12811 ⟨44,by decide⟩).lower ∧ (cell12811 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12811 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12811 ⟨45,by decide⟩).lower ∧ (cell12811 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12811 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12811 ⟨46,by decide⟩).lower ∧ (cell12811 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12811 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12811 ⟨47,by decide⟩).lower ∧ (cell12811 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12811 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12811 ⟨48,by decide⟩).lower ∧ (cell12811 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12811 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12811 ⟨49,by decide⟩).lower ∧ (cell12811 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12811 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12811 ⟨50,by decide⟩).lower ∧ (cell12811 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12811 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12811 ⟨51,by decide⟩).lower ∧ (cell12811 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12811 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12811 ⟨52,by decide⟩).lower ∧ (cell12811 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12811 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12811 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12811 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12811,cell12811,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12811 i).lower ∧
    (cell12811 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12811 i).upper ≤ (0.532 : ℝ) ∧
    (cell12811 i).centre ≤ (0.1 : ℝ) ∧ (cell12811 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12811 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12811 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12811

/-! The local source numeric instances at 12811 have no network premises. -/
namespace BstLean.Part269.N12811
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12811)
open BstLean.Part268 (cell12811)

noncomputable def sourceNumerics12811 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12811 (cell12811 i)
      scalarRow12811.M scalarRow12811.H scalarRow12811.xi := by
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
    energy_allowance := scalarRow12811.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12811]
    centre_nonneg := (scalarRow12811.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12811])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12811
/-! Actual 12812 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12812 ≤ (1.035650985194 : ℝ) := by
  have hr : (113.190105574648 : ℝ) ≤ √(12812 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.190105574648 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12812 12812 (11 / 1000) ≤
    (0.008444969568 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12812) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.190105574648 : ℝ) ≤ √(12812 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12812)
  have hdiv : K / √(12812 : ℝ) ≤ K / 113.190105574648 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.190105574648 ≤ (0.008444969568 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12812.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12812 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12812 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12812 := gPlus_lower 12812
end BstLean.Part269.N12812

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12812
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035650985193 : ℝ) ≤ wn 12812 := by
  have hn : √(12812 : ℝ) ≤ 113.190105574649 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12812 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.190105574649 ≤ 2 / √(12812 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249640833 : ℝ) ≤ rhoBar 12812 BstLean.Part154.csC ∧
    rhoBar 12812 BstLean.Part154.csC ≤ 0.000249641220 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035650985193 : ℝ) / (1.295212 * 12812) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035650985194 : ℝ) / (1.29521 * 12812) := by gcongr
      _ ≤ (0.000249641220 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12812 BstLean.Part154.csC) ≤ 0.000998627201 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12812 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) ≤ 0.000190677569 ∧
    cc1 (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) ≤ 0.000121329420 ∧
    cc2 (rhoBar 12812 BstLean.Part154.csC) ≤ 0.000070432677 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12812 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12812 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12812 BstLean.Part154.csC * nuR (rhoBar 12812 BstLean.Part154.csC)) ≤ 0.000499298021 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249641220 : ℝ) * 0.000998627201 := by gcongr
      _ ≤ (0.000499298021 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12812 BstLean.Part154.csC) * nuR (rhoBar 12812 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998627201 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12812 BstLean.Part154.csC) * rhoBar 12812 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249641220 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249641220 / 2 + 0.399 * 0.000998627201 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190677569 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499298021 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121329420 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249641220 / 1.414213562 := by gcongr
      _ ≤ (0.000070432677 : ℝ) := by norm_num

end BstLean.Part269.N12812

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12812
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) ≤ 1.57013E-7 := by
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12812 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12812 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12812 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190677569 : ℝ) ^ 2 + 0.000121329420 ^ 2 + 3 * 0.000070432677 ^ 2 +
        2 * 0.797885 * 0.000190677569 * 0.000121329420 + 2 * 0.000190677569 * 0.000070432677 +
        4 * 0.797885 * 0.000121329420 * 0.000070432677 := by gcongr
    _ ≤ (1.57013E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12812 BstLean.Part154.csC Θ ≤ 0.002605513949 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12812 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12812 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12812 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035650985194 * 1.57013E-7 / (0.000249640833 : ℝ) := by gcongr
    _ ≤ 0.002605513949 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12812 BstLean.Part154.csC Θ ≤ 0.002890508483 + 0.000658369834 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12812 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12812 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035650985194 : ℝ) * ((2 * Θ * 0.000249641220 +
        (6863 / 10000) * 0.000249641220 * 12812 * 0.000998627201) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002890508483 + 0.000658369834 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12812 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12812 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12812 0.011 Θ ∧ gammaRatio 12812 0.011 Θ ≤ 0.000085820196 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12812 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035650985194 : ℝ) * 0.525 / ((1 - 0.011) * 12812) := by gcongr
      _ ≤ (0.000085820196 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12812 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12812 0.011 Θ) :=
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
    badAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12812 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12812 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12812 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12812 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12812 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12812 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12812 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12812 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12812 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12812 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035650985194 : ℝ) * 12812 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003399312983 + 0.003263883783 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12812

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12812
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12812 BstLean.Part154.csC) (piBar (rhoBar 12812 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12812 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12812 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12812 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12812 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12812 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12812 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12812 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12812 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12812 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12812 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052251923368 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12812) ≤ 0.010550724156 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12812 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035650985194)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010550724156 + 2 * 0.737676 / 12812) := by gcongr
    _ ≤ (0.052251923368 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12812 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12812

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12812
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508588986 : ℝ) ≤ plow 12812 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12812) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619451970)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367894824) : eMP 12812 0.011 xi bn ≤ 0.001177774660 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12812 : ℝ) * (1 - 0.011))) ≤ 0.000582364245 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367894824 / (12812 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582364245 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582364245 : ℝ) + 3.141593 * 0.052619451970 / (12812 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177774660 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619451970)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367894824) : PiBarMP 12812 12 0.011 xi bn ≤ 0.160537468081 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12812 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036985062174 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.565838512401 : ℝ) ≤ √((12812 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.190105574648 : ℝ) ≤ √(12812 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12812) ≤ 0.123088570260 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036985062174 + 0.052619451970 * 1.772454 / (2 * (112.565838512401 : ℝ))) * (1 + 0.001177774660) +
        8 / (12812 * 113.190105574648) + 0.123088570260 := by gcongr
    _ ≤ (0.160537468081 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619451970)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367894824) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281641225582) :
    parallelOracle 12812 0.011 xi bn cd ≤ 0.161518929665 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12812 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12812 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508588986 : ℝ) ≤ plow 12812 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.190105574648 : ℝ) ≤ √(12812 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281641225582 : ℝ) / (2 * 0.560508588986 * 113.190105574648)) * 0.160537468081 +
        0.281641225582 ^ 2 / (2 * 0.560508588986 * 113.190105574648) := by gcongr
    _ ≤ (0.161518929665 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619451970) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367894824)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281641225582) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12812 12812 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508588986 : ℝ) ≤ plow 12812 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.190105574648 : ℝ) ≤ √(12812 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12812 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12812 Θ 1.22 ≤ 0.011715692757 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.190105574648 := by gcongr <;> linarith
      _ ≤ (0.011715692757 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12812 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12812 12812 0.011 ≤ 0.008444969568 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12812 12812 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12812 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12812 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12812 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12812 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161518929665 + 0.011715692757 + (0.008444969568 : ℝ) *
        (1 + 2 * (0.281641225582 + 0.011715692757) / (0.560508588986 * 113.190105574648))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12812]

end BstLean.Part269.N12812

/-! The original eight local profiles supply actual 12812 moment certificates. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12812 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052619451970 ∧
    0 ≤ bN 12812 BstLean.Part154.csC (groupTheta g) ∧ bN 12812 BstLean.Part154.csC (groupTheta g) ≤ 0.001367894824 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12812 12812 0.011
      (momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12812 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12812 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12812 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229389302214 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12812 0.011
      (momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12812 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12812
/-! The actual computed-centre upper energy formula at 12812. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12812

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12812)
open BstLean.Part268 (cell12812)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085170181644
  | 2 => 0.086107196134
  | 3 => 0.087041537391
  | 4 => 0.087974434591
  | 5 => 0.088907380446
  | 6 => 0.089842171112
  | 7 => 0.090780949989
  | 8 => 0.091726255487
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12812 12812 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12812 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12812

/-! Actual upper energy certificates on all 43 source endpoints at 12812. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12812)
open BstLean.Part268 (cell12812)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12812 (gMinus 12812) (1 - (cell12812 i).lower) ≤ 1 ∧
    energyUpper 12812 (gMinus 12812) (BstLean.Part211.gPlus 12812)
      (finiteEnergy 12812 12812 0.011) (1 - (cell12812 i).lower) ≤
      (cell12812 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨10,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨11,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨12,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨13,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨14,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨15,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨16,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨17,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨18,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨19,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨20,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨21,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨22,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨23,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨24,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨25,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨26,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨27,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨28,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨29,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨30,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨31,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨32,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨33,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨34,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨35,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨36,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨37,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨38,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨39,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨40,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨41,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨42,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨43,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨44,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨45,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨46,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨47,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨48,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨49,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨50,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨51,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12812) (by norm_num)
        (q := 1 - (cell12812 ⟨52,by decide⟩).lower)
        (by norm_num [cell12812]) (by norm_num [cell12812])
      exact ⟨E.1,E.2.trans (by norm_num [cell12812])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12812

/-! Source-cell containment and simple scalar guards at 12812. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12812)
open BstLean.Part268 (cell12812)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12812 ⟨10,by decide⟩).lower ∧ (cell12812 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12812 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12812 ⟨11,by decide⟩).lower ∧ (cell12812 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12812 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12812 ⟨12,by decide⟩).lower ∧ (cell12812 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12812 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12812 ⟨13,by decide⟩).lower ∧ (cell12812 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12812 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12812 ⟨14,by decide⟩).lower ∧ (cell12812 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12812 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12812 ⟨15,by decide⟩).lower ∧ (cell12812 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12812 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12812 ⟨16,by decide⟩).lower ∧ (cell12812 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12812 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12812 ⟨17,by decide⟩).lower ∧ (cell12812 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12812 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12812 ⟨18,by decide⟩).lower ∧ (cell12812 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12812 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12812 ⟨19,by decide⟩).lower ∧ (cell12812 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12812 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12812 ⟨20,by decide⟩).lower ∧ (cell12812 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12812 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12812 ⟨21,by decide⟩).lower ∧ (cell12812 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12812 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12812 ⟨22,by decide⟩).lower ∧ (cell12812 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12812 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12812 ⟨23,by decide⟩).lower ∧ (cell12812 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12812 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12812 ⟨24,by decide⟩).lower ∧ (cell12812 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12812 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12812 ⟨25,by decide⟩).lower ∧ (cell12812 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12812 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12812 ⟨26,by decide⟩).lower ∧ (cell12812 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12812 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12812 ⟨27,by decide⟩).lower ∧ (cell12812 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12812 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12812 ⟨28,by decide⟩).lower ∧ (cell12812 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12812 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12812 ⟨29,by decide⟩).lower ∧ (cell12812 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12812 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12812 ⟨30,by decide⟩).lower ∧ (cell12812 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12812 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12812 ⟨31,by decide⟩).lower ∧ (cell12812 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12812 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12812 ⟨32,by decide⟩).lower ∧ (cell12812 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12812 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12812 ⟨33,by decide⟩).lower ∧ (cell12812 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12812 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12812 ⟨34,by decide⟩).lower ∧ (cell12812 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12812 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12812 ⟨35,by decide⟩).lower ∧ (cell12812 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12812 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12812 ⟨36,by decide⟩).lower ∧ (cell12812 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12812 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12812 ⟨37,by decide⟩).lower ∧ (cell12812 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12812 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12812 ⟨38,by decide⟩).lower ∧ (cell12812 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12812 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12812 ⟨39,by decide⟩).lower ∧ (cell12812 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12812 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12812 ⟨40,by decide⟩).lower ∧ (cell12812 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12812 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12812 ⟨41,by decide⟩).lower ∧ (cell12812 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12812 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12812 ⟨42,by decide⟩).lower ∧ (cell12812 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12812 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12812 ⟨43,by decide⟩).lower ∧ (cell12812 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12812 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12812 ⟨44,by decide⟩).lower ∧ (cell12812 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12812 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12812 ⟨45,by decide⟩).lower ∧ (cell12812 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12812 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12812 ⟨46,by decide⟩).lower ∧ (cell12812 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12812 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12812 ⟨47,by decide⟩).lower ∧ (cell12812 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12812 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12812 ⟨48,by decide⟩).lower ∧ (cell12812 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12812 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12812 ⟨49,by decide⟩).lower ∧ (cell12812 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12812 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12812 ⟨50,by decide⟩).lower ∧ (cell12812 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12812 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12812 ⟨51,by decide⟩).lower ∧ (cell12812 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12812 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12812 ⟨52,by decide⟩).lower ∧ (cell12812 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12812 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12812 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12812 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12812,cell12812,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12812 i).lower ∧
    (cell12812 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12812 i).upper ≤ (0.532 : ℝ) ∧
    (cell12812 i).centre ≤ (0.1 : ℝ) ∧ (cell12812 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12812 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12812 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12812

/-! The local source numeric instances at 12812 have no network premises. -/
namespace BstLean.Part269.N12812
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12812)
open BstLean.Part268 (cell12812)

noncomputable def sourceNumerics12812 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12812 (cell12812 i)
      scalarRow12812.M scalarRow12812.H scalarRow12812.xi := by
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
    energy_allowance := scalarRow12812.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12812]
    centre_nonneg := (scalarRow12812.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12812])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12812