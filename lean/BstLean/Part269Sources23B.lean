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
import BstLean.Part269Direction23
import BstLean.Part269Shared23
import BstLean.Part269Finite
import BstLean.Part269Rows23
import BstLean.Part269Source
/-! Actual 12938 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12938 ≤ (1.035475445842 : ℝ) := by
  have hr : (113.745329574448 : ℝ) ≤ √(12938 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.745329574448 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12938 12938 (11 / 1000) ≤
    (0.008403746906 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12938) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.745329574448 : ℝ) ≤ √(12938 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12938)
  have hdiv : K / √(12938 : ℝ) ≤ K / 113.745329574448 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.745329574448 ≤ (0.008403746906 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12938.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12938 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12938 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12938 := gPlus_lower 12938
end BstLean.Part269.N12938

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12938
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035475445841 : ℝ) ≤ wn 12938 := by
  have hn : √(12938 : ℝ) ≤ 113.745329574449 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12938 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.745329574449 ≤ 2 / √(12938 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247167741 : ℝ) ≤ rhoBar 12938 BstLean.Part154.csC ∧
    rhoBar 12938 BstLean.Part154.csC ≤ 0.000247168124 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035475445841 : ℝ) / (1.295212 * 12938) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035475445842 : ℝ) / (1.29521 * 12938) := by gcongr
      _ ≤ (0.000247168124 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12938 BstLean.Part154.csC) ≤ 0.000988733589 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12938 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) ≤ 0.000188788516 ∧
    cc1 (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) ≤ 0.000120127420 ∧
    cc2 (rhoBar 12938 BstLean.Part154.csC) ≤ 0.000069734929 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12938 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12938 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12938 BstLean.Part154.csC * nuR (rhoBar 12938 BstLean.Part154.csC)) ≤ 0.000494351522 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247168124 : ℝ) * 0.000988733589 := by gcongr
      _ ≤ (0.000494351522 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12938 BstLean.Part154.csC) * nuR (rhoBar 12938 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988733589 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12938 BstLean.Part154.csC) * rhoBar 12938 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247168124 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247168124 / 2 + 0.399 * 0.000988733589 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188788516 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494351522 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120127420 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247168124 / 1.414213562 := by gcongr
      _ ≤ (0.000069734929 : ℝ) := by norm_num

end BstLean.Part269.N12938

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12938
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) ≤ 1.53917E-7 := by
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12938 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12938 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12938 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188788516 : ℝ) ^ 2 + 0.000120127420 ^ 2 + 3 * 0.000069734929 ^ 2 +
        2 * 0.797885 * 0.000188788516 * 0.000120127420 + 2 * 0.000188788516 * 0.000069734929 +
        4 * 0.797885 * 0.000120127420 * 0.000069734929 := by gcongr
    _ ≤ (1.53917E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12938 BstLean.Part154.csC Θ ≤ 0.002579256882 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12938 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12938 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12938 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035475445842 * 1.53917E-7 / (0.000247167741 : ℝ) := by gcongr
    _ ≤ 0.002579256882 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12938 BstLean.Part154.csC Θ ≤ 0.002860901525 + 0.000651737141 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12938 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12938 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035475445842 : ℝ) * ((2 * Θ * 0.000247168124 +
        (6863 / 10000) * 0.000247168124 * 12938 * 0.000988733589) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002860901525 + 0.000651737141 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12938 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12938 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12938 0.011 Θ ∧ gammaRatio 12938 0.011 Θ ≤ 0.000084970010 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12938 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035475445842 : ℝ) * 0.525 / ((1 - 0.011) * 12938) := by gcongr
      _ ≤ (0.000084970010 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12938 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12938 0.011 Θ) :=
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
    badAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12938 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12938 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12938 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12938 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12938 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12938 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12938 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12938 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12938 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12938 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035475445842 : ℝ) * 12938 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003281460081 + 0.003230994023 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12938

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12938
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12938 BstLean.Part154.csC) (piBar (rhoBar 12938 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12938 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12938 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12938 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12938 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12938 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12938 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12938 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12938 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12938 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12938 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051994126276 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12938) ≤ 0.010499223006 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12938 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035475445842)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010499223006 + 2 * 0.737676 / 12938) := by gcongr
    _ ≤ (0.051994126276 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12938 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12938

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12938
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514133366 : ℝ) ≤ plow 12938 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12938) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484331944)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354109864) : eMP 12938 0.011 xi bn ≤ 0.001166074138 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12938 : ℝ) * (1 - 0.011))) ≤ 0.000576594098 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354109864 / (12938 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576594098 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576594098 : ℝ) + 3.141593 * 0.052484331944 / (12938 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166074138 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484331944)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354109864) : PiBarMP 12938 12 0.011 xi bn ≤ 0.159745986429 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12938 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036798231806 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.118000335932 : ℝ) ≤ √((12938 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.745329574448 : ℝ) ≤ √(12938 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12938) ≤ 0.122487739188 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036798231806 + 0.052484331944 * 1.772454 / (2 * (113.118000335932 : ℝ))) * (1 + 0.001166074138) +
        8 / (12938 * 113.745329574448) + 0.122487739188 := by gcongr
    _ ≤ (0.159745986429 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484331944)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354109864) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281088717972) :
    parallelOracle 12938 0.011 xi bn cd ≤ 0.160717768886 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12938 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12938 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514133366 : ℝ) ≤ plow 12938 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.745329574448 : ℝ) ≤ √(12938 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281088717972 : ℝ) / (2 * 0.560514133366 * 113.745329574448)) * 0.159745986429 +
        0.281088717972 ^ 2 / (2 * 0.560514133366 * 113.745329574448) := by gcongr
    _ ≤ (0.160717768886 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484331944) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354109864)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281088717972) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12938 12938 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514133366 : ℝ) ≤ plow 12938 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.745329574448 : ℝ) ≤ √(12938 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12938 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12938 Θ 1.22 ≤ 0.011658505057 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.745329574448 := by gcongr <;> linarith
      _ ≤ (0.011658505057 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12938 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12938 12938 0.011 ≤ 0.008403746906 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12938 12938 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12938 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12938 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12938 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12938 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160717768886 + 0.011658505057 + (0.008403746906 : ℝ) *
        (1 + 2 * (0.281088717972 + 0.011658505057) / (0.560514133366 * 113.745329574448))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12938]

end BstLean.Part269.N12938

/-! The original eight local profiles supply actual 12938 moment certificates. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12938 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052484331944 ∧
    0 ≤ bN 12938 BstLean.Part154.csC (groupTheta g) ∧ bN 12938 BstLean.Part154.csC (groupTheta g) ≤ 0.001354109864 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12938 12938 0.011
      (momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12938 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12938 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12938 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229094591696 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12938 0.011
      (momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12938 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12938
/-! The actual computed-centre upper energy formula at 12938. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12938

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12938)
open BstLean.Part268 (cell12938)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084824588564
  | 2 => 0.085755726321
  | 3 => 0.086683411607
  | 4 => 0.087608689022
  | 5 => 0.088532833257
  | 6 => 0.089457384671
  | 7 => 0.090384188483
  | 8 => 0.091315437664
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12938 12938 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12938 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12938

/-! Actual upper energy certificates on all 43 source endpoints at 12938. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12938)
open BstLean.Part268 (cell12938)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12938 (gMinus 12938) (1 - (cell12938 i).lower) ≤ 1 ∧
    energyUpper 12938 (gMinus 12938) (BstLean.Part211.gPlus 12938)
      (finiteEnergy 12938 12938 0.011) (1 - (cell12938 i).lower) ≤
      (cell12938 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨10,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨11,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨12,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨13,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨14,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨15,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨16,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨17,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨18,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨19,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨20,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨21,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨22,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨23,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨24,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨25,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨26,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨27,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨28,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨29,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨30,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨31,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨32,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨33,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨34,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨35,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨36,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨37,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨38,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨39,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨40,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨41,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨42,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨43,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨44,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨45,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨46,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨47,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨48,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨49,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨50,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨51,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12938) (by norm_num)
        (q := 1 - (cell12938 ⟨52,by decide⟩).lower)
        (by norm_num [cell12938]) (by norm_num [cell12938])
      exact ⟨E.1,E.2.trans (by norm_num [cell12938])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12938

/-! Source-cell containment and simple scalar guards at 12938. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12938)
open BstLean.Part268 (cell12938)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12938 ⟨10,by decide⟩).lower ∧ (cell12938 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12938 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12938 ⟨11,by decide⟩).lower ∧ (cell12938 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12938 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12938 ⟨12,by decide⟩).lower ∧ (cell12938 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12938 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12938 ⟨13,by decide⟩).lower ∧ (cell12938 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12938 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12938 ⟨14,by decide⟩).lower ∧ (cell12938 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12938 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12938 ⟨15,by decide⟩).lower ∧ (cell12938 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12938 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12938 ⟨16,by decide⟩).lower ∧ (cell12938 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12938 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12938 ⟨17,by decide⟩).lower ∧ (cell12938 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12938 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12938 ⟨18,by decide⟩).lower ∧ (cell12938 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12938 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12938 ⟨19,by decide⟩).lower ∧ (cell12938 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12938 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12938 ⟨20,by decide⟩).lower ∧ (cell12938 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12938 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12938 ⟨21,by decide⟩).lower ∧ (cell12938 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12938 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12938 ⟨22,by decide⟩).lower ∧ (cell12938 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12938 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12938 ⟨23,by decide⟩).lower ∧ (cell12938 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12938 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12938 ⟨24,by decide⟩).lower ∧ (cell12938 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12938 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12938 ⟨25,by decide⟩).lower ∧ (cell12938 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12938 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12938 ⟨26,by decide⟩).lower ∧ (cell12938 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12938 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12938 ⟨27,by decide⟩).lower ∧ (cell12938 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12938 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12938 ⟨28,by decide⟩).lower ∧ (cell12938 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12938 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12938 ⟨29,by decide⟩).lower ∧ (cell12938 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12938 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12938 ⟨30,by decide⟩).lower ∧ (cell12938 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12938 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12938 ⟨31,by decide⟩).lower ∧ (cell12938 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12938 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12938 ⟨32,by decide⟩).lower ∧ (cell12938 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12938 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12938 ⟨33,by decide⟩).lower ∧ (cell12938 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12938 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12938 ⟨34,by decide⟩).lower ∧ (cell12938 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12938 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12938 ⟨35,by decide⟩).lower ∧ (cell12938 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12938 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12938 ⟨36,by decide⟩).lower ∧ (cell12938 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12938 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12938 ⟨37,by decide⟩).lower ∧ (cell12938 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12938 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12938 ⟨38,by decide⟩).lower ∧ (cell12938 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12938 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12938 ⟨39,by decide⟩).lower ∧ (cell12938 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12938 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12938 ⟨40,by decide⟩).lower ∧ (cell12938 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12938 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12938 ⟨41,by decide⟩).lower ∧ (cell12938 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12938 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12938 ⟨42,by decide⟩).lower ∧ (cell12938 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12938 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12938 ⟨43,by decide⟩).lower ∧ (cell12938 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12938 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12938 ⟨44,by decide⟩).lower ∧ (cell12938 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12938 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12938 ⟨45,by decide⟩).lower ∧ (cell12938 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12938 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12938 ⟨46,by decide⟩).lower ∧ (cell12938 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12938 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12938 ⟨47,by decide⟩).lower ∧ (cell12938 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12938 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12938 ⟨48,by decide⟩).lower ∧ (cell12938 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12938 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12938 ⟨49,by decide⟩).lower ∧ (cell12938 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12938 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12938 ⟨50,by decide⟩).lower ∧ (cell12938 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12938 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12938 ⟨51,by decide⟩).lower ∧ (cell12938 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12938 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12938 ⟨52,by decide⟩).lower ∧ (cell12938 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12938 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12938 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12938 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12938,cell12938,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12938 i).lower ∧
    (cell12938 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12938 i).upper ≤ (0.532 : ℝ) ∧
    (cell12938 i).centre ≤ (0.1 : ℝ) ∧ (cell12938 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12938 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12938 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12938

/-! The local source numeric instances at 12938 have no network premises. -/
namespace BstLean.Part269.N12938
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12938)
open BstLean.Part268 (cell12938)

noncomputable def sourceNumerics12938 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12938 (cell12938 i)
      scalarRow12938.M scalarRow12938.H scalarRow12938.xi := by
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
    energy_allowance := scalarRow12938.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12938]
    centre_nonneg := (scalarRow12938.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12938])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12938
/-! Actual 12939 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12939 ≤ (1.035474062996 : ℝ) := by
  have hr : (113.749725274393 : ℝ) ≤ √(12939 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.749725274393 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12939 12939 (11 / 1000) ≤
    (0.008403422153 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12939) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.749725274393 : ℝ) ≤ √(12939 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12939)
  have hdiv : K / √(12939 : ℝ) ≤ K / 113.749725274393 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.749725274393 ≤ (0.008403422153 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12939.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12939 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12939 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12939 := gPlus_lower 12939
end BstLean.Part269.N12939

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12939
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035474062995 : ℝ) ≤ wn 12939 := by
  have hn : √(12939 : ℝ) ≤ 113.749725274394 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12939 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.749725274394 ≤ 2 / √(12939 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247148309 : ℝ) ≤ rhoBar 12939 BstLean.Part154.csC ∧
    rhoBar 12939 BstLean.Part154.csC ≤ 0.000247148691 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035474062995 : ℝ) / (1.295212 * 12939) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035474062996 : ℝ) / (1.29521 * 12939) := by gcongr
      _ ≤ (0.000247148691 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12939 BstLean.Part154.csC) ≤ 0.000988655847 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12939 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) ≤ 0.000188773672 ∧
    cc1 (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) ≤ 0.000120117975 ∧
    cc2 (rhoBar 12939 BstLean.Part154.csC) ≤ 0.000069729446 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12939 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12939 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12939 BstLean.Part154.csC * nuR (rhoBar 12939 BstLean.Part154.csC)) ≤ 0.000494312653 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247148691 : ℝ) * 0.000988655847 := by gcongr
      _ ≤ (0.000494312653 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12939 BstLean.Part154.csC) * nuR (rhoBar 12939 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988655847 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12939 BstLean.Part154.csC) * rhoBar 12939 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247148691 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247148691 / 2 + 0.399 * 0.000988655847 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188773672 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494312653 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120117975 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247148691 / 1.414213562 := by gcongr
      _ ≤ (0.000069729446 : ℝ) := by norm_num

end BstLean.Part269.N12939

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12939
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) ≤ 1.53893E-7 := by
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12939 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12939 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12939 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188773672 : ℝ) ^ 2 + 0.000120117975 ^ 2 + 3 * 0.000069729446 ^ 2 +
        2 * 0.797885 * 0.000188773672 * 0.000120117975 + 2 * 0.000188773672 * 0.000069729446 +
        4 * 0.797885 * 0.000120117975 * 0.000069729446 := by gcongr
    _ ≤ (1.53893E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12939 BstLean.Part154.csC Θ ≤ 0.002579054021 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12939 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12939 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12939 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035474062996 * 1.53893E-7 / (0.000247148309 : ℝ) := by gcongr
    _ ≤ 0.002579054021 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12939 BstLean.Part154.csC Θ ≤ 0.002860668933 + 0.000651685030 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12939 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12939 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035474062996 : ℝ) * ((2 * Θ * 0.000247148691 +
        (6863 / 10000) * 0.000247148691 * 12939 * 0.000988655847) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002860668933 + 0.000651685030 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12939 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12939 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12939 0.011 Θ ∧ gammaRatio 12939 0.011 Θ ≤ 0.000084963329 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12939 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035474062996 : ℝ) * 0.525 / ((1 - 0.011) * 12939) := by gcongr
      _ ≤ (0.000084963329 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12939 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12939 0.011 Θ) :=
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
    badAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12939 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12939 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12939 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12939 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12939 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12939 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12939 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12939 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12939 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12939 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035474062996 : ℝ) * 12939 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003281227489 + 0.003230739051 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12939

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12939
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12939 BstLean.Part154.csC) (piBar (rhoBar 12939 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12939 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12939 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12939 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12939 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12939 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12939 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12939 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12939 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12939 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12939 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051992095447 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12939) ≤ 0.010498817278 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12939 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035474062996)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010498817278 + 2 * 0.737676 / 12939) := by gcongr
    _ ≤ (0.051992095447 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12939 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12939

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12939
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514176937 : ℝ) ≤ plow 12939 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12939) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483965491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354003362) : eMP 12939 0.011 xi bn ≤ 0.001165983138 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12939 : ℝ) * (1 - 0.011))) ≤ 0.000576549141 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354003362 / (12939 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576549141 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576549141 : ℝ) + 3.141593 * 0.052483965491 / (12939 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165983138 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483965491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354003362) : PiBarMP 12939 12 0.011 xi bn ≤ 0.159739781439 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12939 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036796784670 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.122371792674 : ℝ) ≤ √((12939 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.749725274393 : ℝ) ≤ √(12939 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12939) ≤ 0.122483005820 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036796784670 + 0.052483965491 * 1.772454 / (2 * (113.122371792674 : ℝ))) * (1 + 0.001165983138) +
        8 / (12939 * 113.749725274393) + 0.122483005820 := by gcongr
    _ ≤ (0.159739781439 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483965491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354003362) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281085887356) :
    parallelOracle 12939 0.011 xi bn cd ≤ 0.160711496564 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12939 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12939 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514176937 : ℝ) ≤ plow 12939 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.749725274393 : ℝ) ≤ √(12939 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281085887356 : ℝ) / (2 * 0.560514176937 * 113.749725274393)) * 0.159739781439 +
        0.281085887356 ^ 2 / (2 * 0.560514176937 * 113.749725274393) := by gcongr
    _ ≤ (0.160711496564 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483965491) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354003362)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281085887356) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12939 12939 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514176937 : ℝ) ≤ plow 12939 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.749725274393 : ℝ) ≤ √(12939 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12939 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12939 Θ 1.22 ≤ 0.011658054530 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.749725274393 := by gcongr <;> linarith
      _ ≤ (0.011658054530 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12939 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12939 12939 0.011 ≤ 0.008403422153 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12939 12939 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12939 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12939 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12939 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12939 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160711496564 + 0.011658054530 + (0.008403422153 : ℝ) *
        (1 + 2 * (0.281085887356 + 0.011658054530) / (0.560514176937 * 113.749725274393))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12939]

end BstLean.Part269.N12939

/-! The original eight local profiles supply actual 12939 moment certificates. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12939 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052483965491 ∧
    0 ≤ bN 12939 BstLean.Part154.csC (groupTheta g) ∧ bN 12939 BstLean.Part154.csC (groupTheta g) ≤ 0.001354003362 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12939 12939 0.011
      (momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12939 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12939 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12939 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229093791909 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12939 0.011
      (momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12939 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12939
/-! The actual computed-centre upper energy formula at 12939. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12939

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12939)
open BstLean.Part268 (cell12939)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084821902527
  | 2 => 0.085752995838
  | 3 => 0.086680631010
  | 4 => 0.087605851286
  | 5 => 0.088529929751
  | 6 => 0.089454404879
  | 7 => 0.090381119685
  | 8 => 0.091312264586
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12939 12939 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12939 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12939

/-! Actual upper energy certificates on all 43 source endpoints at 12939. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12939)
open BstLean.Part268 (cell12939)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12939 (gMinus 12939) (1 - (cell12939 i).lower) ≤ 1 ∧
    energyUpper 12939 (gMinus 12939) (BstLean.Part211.gPlus 12939)
      (finiteEnergy 12939 12939 0.011) (1 - (cell12939 i).lower) ≤
      (cell12939 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨10,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨11,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨12,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨13,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨14,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨15,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨16,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨17,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨18,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨19,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨20,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨21,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨22,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨23,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨24,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨25,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨26,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨27,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨28,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨29,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨30,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨31,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨32,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨33,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨34,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨35,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨36,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨37,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨38,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨39,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨40,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨41,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨42,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨43,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨44,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨45,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨46,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨47,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨48,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨49,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨50,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨51,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12939) (by norm_num)
        (q := 1 - (cell12939 ⟨52,by decide⟩).lower)
        (by norm_num [cell12939]) (by norm_num [cell12939])
      exact ⟨E.1,E.2.trans (by norm_num [cell12939])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12939

/-! Source-cell containment and simple scalar guards at 12939. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12939)
open BstLean.Part268 (cell12939)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12939 ⟨10,by decide⟩).lower ∧ (cell12939 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12939 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12939 ⟨11,by decide⟩).lower ∧ (cell12939 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12939 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12939 ⟨12,by decide⟩).lower ∧ (cell12939 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12939 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12939 ⟨13,by decide⟩).lower ∧ (cell12939 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12939 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12939 ⟨14,by decide⟩).lower ∧ (cell12939 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12939 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12939 ⟨15,by decide⟩).lower ∧ (cell12939 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12939 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12939 ⟨16,by decide⟩).lower ∧ (cell12939 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12939 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12939 ⟨17,by decide⟩).lower ∧ (cell12939 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12939 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12939 ⟨18,by decide⟩).lower ∧ (cell12939 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12939 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12939 ⟨19,by decide⟩).lower ∧ (cell12939 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12939 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12939 ⟨20,by decide⟩).lower ∧ (cell12939 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12939 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12939 ⟨21,by decide⟩).lower ∧ (cell12939 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12939 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12939 ⟨22,by decide⟩).lower ∧ (cell12939 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12939 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12939 ⟨23,by decide⟩).lower ∧ (cell12939 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12939 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12939 ⟨24,by decide⟩).lower ∧ (cell12939 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12939 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12939 ⟨25,by decide⟩).lower ∧ (cell12939 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12939 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12939 ⟨26,by decide⟩).lower ∧ (cell12939 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12939 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12939 ⟨27,by decide⟩).lower ∧ (cell12939 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12939 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12939 ⟨28,by decide⟩).lower ∧ (cell12939 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12939 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12939 ⟨29,by decide⟩).lower ∧ (cell12939 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12939 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12939 ⟨30,by decide⟩).lower ∧ (cell12939 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12939 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12939 ⟨31,by decide⟩).lower ∧ (cell12939 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12939 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12939 ⟨32,by decide⟩).lower ∧ (cell12939 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12939 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12939 ⟨33,by decide⟩).lower ∧ (cell12939 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12939 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12939 ⟨34,by decide⟩).lower ∧ (cell12939 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12939 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12939 ⟨35,by decide⟩).lower ∧ (cell12939 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12939 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12939 ⟨36,by decide⟩).lower ∧ (cell12939 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12939 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12939 ⟨37,by decide⟩).lower ∧ (cell12939 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12939 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12939 ⟨38,by decide⟩).lower ∧ (cell12939 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12939 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12939 ⟨39,by decide⟩).lower ∧ (cell12939 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12939 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12939 ⟨40,by decide⟩).lower ∧ (cell12939 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12939 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12939 ⟨41,by decide⟩).lower ∧ (cell12939 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12939 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12939 ⟨42,by decide⟩).lower ∧ (cell12939 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12939 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12939 ⟨43,by decide⟩).lower ∧ (cell12939 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12939 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12939 ⟨44,by decide⟩).lower ∧ (cell12939 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12939 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12939 ⟨45,by decide⟩).lower ∧ (cell12939 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12939 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12939 ⟨46,by decide⟩).lower ∧ (cell12939 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12939 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12939 ⟨47,by decide⟩).lower ∧ (cell12939 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12939 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12939 ⟨48,by decide⟩).lower ∧ (cell12939 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12939 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12939 ⟨49,by decide⟩).lower ∧ (cell12939 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12939 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12939 ⟨50,by decide⟩).lower ∧ (cell12939 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12939 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12939 ⟨51,by decide⟩).lower ∧ (cell12939 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12939 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12939 ⟨52,by decide⟩).lower ∧ (cell12939 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12939 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12939 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12939 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12939,cell12939,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12939 i).lower ∧
    (cell12939 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12939 i).upper ≤ (0.532 : ℝ) ∧
    (cell12939 i).centre ≤ (0.1 : ℝ) ∧ (cell12939 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12939 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12939 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12939

/-! The local source numeric instances at 12939 have no network premises. -/
namespace BstLean.Part269.N12939
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12939)
open BstLean.Part268 (cell12939)

noncomputable def sourceNumerics12939 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12939 (cell12939 i)
      scalarRow12939.M scalarRow12939.H scalarRow12939.xi := by
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
    energy_allowance := scalarRow12939.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12939]
    centre_nonneg := (scalarRow12939.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12939])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12939
/-! Actual 12940 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12940 ≤ (1.035472680311 : ℝ) := by
  have hr : (113.754120804478 : ℝ) ≤ √(12940 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.754120804478 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12940 12940 (11 / 1000) ≤
    (0.008403097437 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12940) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.754120804478 : ℝ) ≤ √(12940 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12940)
  have hdiv : K / √(12940 : ℝ) ≤ K / 113.754120804478 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.754120804478 ≤ (0.008403097437 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12940.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12940 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12940 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12940 := gPlus_lower 12940
end BstLean.Part269.N12940

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12940
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035472680310 : ℝ) ≤ wn 12940 := by
  have hn : √(12940 : ℝ) ≤ 113.754120804479 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12940 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.754120804479 ≤ 2 / √(12940 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247128879 : ℝ) ≤ rhoBar 12940 BstLean.Part154.csC ∧
    rhoBar 12940 BstLean.Part154.csC ≤ 0.000247129262 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035472680310 : ℝ) / (1.295212 * 12940) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035472680311 : ℝ) / (1.29521 * 12940) := by gcongr
      _ ≤ (0.000247129262 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12940 BstLean.Part154.csC) ≤ 0.000988578121 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12940 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) ≤ 0.000188758832 ∧
    cc1 (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) ≤ 0.000120108532 ∧
    cc2 (rhoBar 12940 BstLean.Part154.csC) ≤ 0.000069723965 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12940 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12940 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12940 BstLean.Part154.csC * nuR (rhoBar 12940 BstLean.Part154.csC)) ≤ 0.000494273793 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247129262 : ℝ) * 0.000988578121 := by gcongr
      _ ≤ (0.000494273793 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12940 BstLean.Part154.csC) * nuR (rhoBar 12940 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988578121 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12940 BstLean.Part154.csC) * rhoBar 12940 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247129262 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247129262 / 2 + 0.399 * 0.000988578121 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188758832 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494273793 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120108532 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247129262 / 1.414213562 := by gcongr
      _ ≤ (0.000069723965 : ℝ) := by norm_num

end BstLean.Part269.N12940

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12940
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) ≤ 1.53869E-7 := by
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12940 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12940 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12940 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188758832 : ℝ) ^ 2 + 0.000120108532 ^ 2 + 3 * 0.000069723965 ^ 2 +
        2 * 0.797885 * 0.000188758832 * 0.000120108532 + 2 * 0.000188758832 * 0.000069723965 +
        4 * 0.797885 * 0.000120108532 * 0.000069723965 := by gcongr
    _ ≤ (1.53869E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12940 BstLean.Part154.csC Θ ≤ 0.002578851108 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12940 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12940 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12940 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035472680311 * 1.53869E-7 / (0.000247128879 : ℝ) := by gcongr
    _ ≤ 0.002578851108 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12940 BstLean.Part154.csC Θ ≤ 0.002860436401 + 0.000651632929 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12940 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12940 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035472680311 : ℝ) * ((2 * Θ * 0.000247129262 +
        (6863 / 10000) * 0.000247129262 * 12940 * 0.000988578121) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002860436401 + 0.000651632929 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12940 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12940 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12940 0.011 Θ ∧ gammaRatio 12940 0.011 Θ ≤ 0.000084956650 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12940 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035472680311 : ℝ) * 0.525 / ((1 - 0.011) * 12940) := by gcongr
      _ ≤ (0.000084956650 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12940 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12940 0.011 Θ) :=
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
    badAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12940 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12940 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12940 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12940 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12940 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12940 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12940 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12940 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12940 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12940 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035472680311 : ℝ) * 12940 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003280994957 + 0.003230484037 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12940

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12940
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12940 BstLean.Part154.csC) (piBar (rhoBar 12940 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12940 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12940 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12940 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12940 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12940 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12940 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12940 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12940 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12940 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12940 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051990064856 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12940) ≤ 0.010498411597 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12940 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035472680311)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010498411597 + 2 * 0.737676 / 12940) := by gcongr
    _ ≤ (0.051990064856 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12940 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12940

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12940
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514220502 : ℝ) ≤ plow 12940 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12940) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483599077)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353896832) : eMP 12940 0.011 xi bn ≤ 0.001165892136 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12940 : ℝ) * (1 - 0.011))) ≤ 0.000576504183 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353896832 / (12940 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576504183 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576504183 : ℝ) + 3.141593 * 0.052483599077 / (12940 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165892136 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483599077)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353896832) : PiBarMP 12940 12 0.011 xi bn ≤ 0.159733576561 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12940 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036795337096 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.126743080493 : ℝ) ≤ √((12940 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.754120804478 : ℝ) ≤ √(12940 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12940) ≤ 0.122478273000 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036795337096 + 0.052483599077 * 1.772454 / (2 * (113.126743080493 : ℝ))) * (1 + 0.001165892136) +
        8 / (12940 * 113.754120804478) + 0.122478273000 := by gcongr
    _ ≤ (0.159733576561 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483599077)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353896832) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281083057061) :
    parallelOracle 12940 0.011 xi bn cd ≤ 0.160705224364 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12940 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12940 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514220502 : ℝ) ≤ plow 12940 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.754120804478 : ℝ) ≤ √(12940 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281083057061 : ℝ) / (2 * 0.560514220502 * 113.754120804478)) * 0.159733576561 +
        0.281083057061 ^ 2 / (2 * 0.560514220502 * 113.754120804478) := by gcongr
    _ ≤ (0.160705224364 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483599077) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353896832)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281083057061) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12940 12940 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514220502 : ℝ) ≤ plow 12940 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.754120804478 : ℝ) ≤ √(12940 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12940 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12940 Θ 1.22 ≤ 0.011657604056 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.754120804478 := by gcongr <;> linarith
      _ ≤ (0.011657604056 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12940 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12940 12940 0.011 ≤ 0.008403097437 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12940 12940 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12940 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12940 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12940 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12940 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160705224364 + 0.011657604056 + (0.008403097437 : ℝ) *
        (1 + 2 * (0.281083057061 + 0.011657604056) / (0.560514220502 * 113.754120804478))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12940]

end BstLean.Part269.N12940

/-! The original eight local profiles supply actual 12940 moment certificates. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12940 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052483599077 ∧
    0 ≤ bN 12940 BstLean.Part154.csC (groupTheta g) ∧ bN 12940 BstLean.Part154.csC (groupTheta g) ≤ 0.001353896832 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12940 12940 0.011
      (momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12940 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12940 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12940 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229092992205 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12940 0.011
      (momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12940 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12940
/-! The actual computed-centre upper energy formula at 12940. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12940

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12940)
open BstLean.Part268 (cell12940)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084819217347
  | 2 => 0.085750266245
  | 3 => 0.086677851344
  | 4 => 0.087603014531
  | 5 => 0.088527027287
  | 6 => 0.089451426202
  | 7 => 0.090378052093
  | 8 => 0.091309092823
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12940 12940 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12940 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12940

/-! Actual upper energy certificates on all 43 source endpoints at 12940. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12940)
open BstLean.Part268 (cell12940)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12940 (gMinus 12940) (1 - (cell12940 i).lower) ≤ 1 ∧
    energyUpper 12940 (gMinus 12940) (BstLean.Part211.gPlus 12940)
      (finiteEnergy 12940 12940 0.011) (1 - (cell12940 i).lower) ≤
      (cell12940 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨10,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨11,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨12,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨13,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨14,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨15,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨16,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨17,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨18,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨19,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨20,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨21,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨22,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨23,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨24,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨25,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨26,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨27,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨28,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨29,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨30,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨31,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨32,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨33,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨34,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨35,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨36,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨37,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨38,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨39,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨40,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨41,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨42,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨43,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨44,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨45,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨46,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨47,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨48,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨49,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨50,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨51,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12940) (by norm_num)
        (q := 1 - (cell12940 ⟨52,by decide⟩).lower)
        (by norm_num [cell12940]) (by norm_num [cell12940])
      exact ⟨E.1,E.2.trans (by norm_num [cell12940])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12940

/-! Source-cell containment and simple scalar guards at 12940. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12940)
open BstLean.Part268 (cell12940)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12940 ⟨10,by decide⟩).lower ∧ (cell12940 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12940 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12940 ⟨11,by decide⟩).lower ∧ (cell12940 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12940 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12940 ⟨12,by decide⟩).lower ∧ (cell12940 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12940 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12940 ⟨13,by decide⟩).lower ∧ (cell12940 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12940 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12940 ⟨14,by decide⟩).lower ∧ (cell12940 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12940 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12940 ⟨15,by decide⟩).lower ∧ (cell12940 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12940 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12940 ⟨16,by decide⟩).lower ∧ (cell12940 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12940 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12940 ⟨17,by decide⟩).lower ∧ (cell12940 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12940 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12940 ⟨18,by decide⟩).lower ∧ (cell12940 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12940 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12940 ⟨19,by decide⟩).lower ∧ (cell12940 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12940 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12940 ⟨20,by decide⟩).lower ∧ (cell12940 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12940 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12940 ⟨21,by decide⟩).lower ∧ (cell12940 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12940 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12940 ⟨22,by decide⟩).lower ∧ (cell12940 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12940 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12940 ⟨23,by decide⟩).lower ∧ (cell12940 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12940 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12940 ⟨24,by decide⟩).lower ∧ (cell12940 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12940 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12940 ⟨25,by decide⟩).lower ∧ (cell12940 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12940 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12940 ⟨26,by decide⟩).lower ∧ (cell12940 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12940 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12940 ⟨27,by decide⟩).lower ∧ (cell12940 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12940 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12940 ⟨28,by decide⟩).lower ∧ (cell12940 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12940 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12940 ⟨29,by decide⟩).lower ∧ (cell12940 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12940 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12940 ⟨30,by decide⟩).lower ∧ (cell12940 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12940 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12940 ⟨31,by decide⟩).lower ∧ (cell12940 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12940 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12940 ⟨32,by decide⟩).lower ∧ (cell12940 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12940 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12940 ⟨33,by decide⟩).lower ∧ (cell12940 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12940 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12940 ⟨34,by decide⟩).lower ∧ (cell12940 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12940 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12940 ⟨35,by decide⟩).lower ∧ (cell12940 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12940 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12940 ⟨36,by decide⟩).lower ∧ (cell12940 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12940 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12940 ⟨37,by decide⟩).lower ∧ (cell12940 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12940 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12940 ⟨38,by decide⟩).lower ∧ (cell12940 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12940 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12940 ⟨39,by decide⟩).lower ∧ (cell12940 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12940 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12940 ⟨40,by decide⟩).lower ∧ (cell12940 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12940 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12940 ⟨41,by decide⟩).lower ∧ (cell12940 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12940 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12940 ⟨42,by decide⟩).lower ∧ (cell12940 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12940 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12940 ⟨43,by decide⟩).lower ∧ (cell12940 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12940 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12940 ⟨44,by decide⟩).lower ∧ (cell12940 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12940 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12940 ⟨45,by decide⟩).lower ∧ (cell12940 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12940 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12940 ⟨46,by decide⟩).lower ∧ (cell12940 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12940 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12940 ⟨47,by decide⟩).lower ∧ (cell12940 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12940 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12940 ⟨48,by decide⟩).lower ∧ (cell12940 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12940 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12940 ⟨49,by decide⟩).lower ∧ (cell12940 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12940 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12940 ⟨50,by decide⟩).lower ∧ (cell12940 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12940 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12940 ⟨51,by decide⟩).lower ∧ (cell12940 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12940 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12940 ⟨52,by decide⟩).lower ∧ (cell12940 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12940 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12940 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12940 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12940,cell12940,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12940 i).lower ∧
    (cell12940 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12940 i).upper ≤ (0.532 : ℝ) ∧
    (cell12940 i).centre ≤ (0.1 : ℝ) ∧ (cell12940 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12940 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12940 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12940

/-! The local source numeric instances at 12940 have no network premises. -/
namespace BstLean.Part269.N12940
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12940)
open BstLean.Part268 (cell12940)

noncomputable def sourceNumerics12940 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12940 (cell12940 i)
      scalarRow12940.M scalarRow12940.H scalarRow12940.xi := by
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
    energy_allowance := scalarRow12940.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12940]
    centre_nonneg := (scalarRow12940.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12940])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12940
/-! Actual 12941 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12941 ≤ (1.035471297787 : ℝ) := by
  have hr : (113.758516164725 : ℝ) ≤ √(12941 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.758516164725 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12941 12941 (11 / 1000) ≤
    (0.008402772759 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12941) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.758516164725 : ℝ) ≤ √(12941 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12941)
  have hdiv : K / √(12941 : ℝ) ≤ K / 113.758516164725 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.758516164725 ≤ (0.008402772759 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12941.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12941 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12941 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12941 := gPlus_lower 12941
end BstLean.Part269.N12941

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12941
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035471297786 : ℝ) ≤ wn 12941 := by
  have hn : √(12941 : ℝ) ≤ 113.758516164726 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12941 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.758516164726 ≤ 2 / √(12941 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247109453 : ℝ) ≤ rhoBar 12941 BstLean.Part154.csC ∧
    rhoBar 12941 BstLean.Part154.csC ≤ 0.000247109835 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035471297786 : ℝ) / (1.295212 * 12941) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035471297787 : ℝ) / (1.29521 * 12941) := by gcongr
      _ ≤ (0.000247109835 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12941 BstLean.Part154.csC) ≤ 0.000988500404 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12941 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) ≤ 0.000188743993 ∧
    cc1 (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) ≤ 0.000120099090 ∧
    cc2 (rhoBar 12941 BstLean.Part154.csC) ≤ 0.000069718483 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12941 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12941 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12941 BstLean.Part154.csC * nuR (rhoBar 12941 BstLean.Part154.csC)) ≤ 0.000494234936 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247109835 : ℝ) * 0.000988500404 := by gcongr
      _ ≤ (0.000494234936 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12941 BstLean.Part154.csC) * nuR (rhoBar 12941 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988500404 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12941 BstLean.Part154.csC) * rhoBar 12941 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247109835 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247109835 / 2 + 0.399 * 0.000988500404 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188743993 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494234936 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120099090 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247109835 / 1.414213562 := by gcongr
      _ ≤ (0.000069718483 : ℝ) := by norm_num

end BstLean.Part269.N12941

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12941
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) ≤ 1.53845E-7 := by
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12941 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12941 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12941 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188743993 : ℝ) ^ 2 + 0.000120099090 ^ 2 + 3 * 0.000069718483 ^ 2 +
        2 * 0.797885 * 0.000188743993 * 0.000120099090 + 2 * 0.000188743993 * 0.000069718483 +
        4 * 0.797885 * 0.000120099090 * 0.000069718483 := by gcongr
    _ ≤ (1.53845E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12941 BstLean.Part154.csC Θ ≤ 0.002578648124 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12941 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12941 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12941 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035471297787 * 1.53845E-7 / (0.000247109453 : ℝ) := by gcongr
    _ ≤ 0.002578648124 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12941 BstLean.Part154.csC Θ ≤ 0.002860203885 + 0.000651580834 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12941 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12941 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035471297787 : ℝ) * ((2 * Θ * 0.000247109835 +
        (6863 / 10000) * 0.000247109835 * 12941 * 0.000988500404) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002860203885 + 0.000651580834 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12941 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12941 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12941 0.011 Θ ∧ gammaRatio 12941 0.011 Θ ≤ 0.000084949972 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12941 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035471297787 : ℝ) * 0.525 / ((1 - 0.011) * 12941) := by gcongr
      _ ≤ (0.000084949972 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12941 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12941 0.011 Θ) :=
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
    badAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12941 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12941 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12941 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12941 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12941 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12941 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12941 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12941 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12941 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12941 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035471297787 : ℝ) * 12941 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003280762441 + 0.003230228958 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12941

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12941
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12941 BstLean.Part154.csC) (piBar (rhoBar 12941 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12941 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12941 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12941 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12941 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12941 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12941 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12941 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12941 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12941 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12941 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051988034506 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12941) ≤ 0.010498005964 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12941 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035471297787)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010498005964 + 2 * 0.737676 / 12941) := by gcongr
    _ ≤ (0.051988034506 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12941 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12941

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12941
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514264059 : ℝ) ≤ plow 12941 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12941) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483232644)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353790266) : eMP 12941 0.011 xi bn ≤ 0.001165801125 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12941 : ℝ) * (1 - 0.011))) ≤ 0.000576459220 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353790266 / (12941 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576459220 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576459220 : ℝ) + 3.141593 * 0.052483232644 / (12941 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165801125 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483232644)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353790266) : PiBarMP 12941 12 0.011 xi bn ≤ 0.159727371688 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12941 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036793888977 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.131114199410 : ℝ) ≤ √((12941 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.758516164725 : ℝ) ≤ √(12941 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12941) ≤ 0.122473540729 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036793888977 + 0.052483232644 * 1.772454 / (2 * (113.131114199410 : ℝ))) * (1 + 0.001165801125) +
        8 / (12941 * 113.758516164725) + 0.122473540729 := by gcongr
    _ ≤ (0.159727371688 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483232644)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353790266) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281080226962) :
    parallelOracle 12941 0.011 xi bn cd ≤ 0.160698952177 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12941 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12941 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514264059 : ℝ) ≤ plow 12941 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.758516164725 : ℝ) ≤ √(12941 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281080226962 : ℝ) / (2 * 0.560514264059 * 113.758516164725)) * 0.159727371688 +
        0.281080226962 ^ 2 / (2 * 0.560514264059 * 113.758516164725) := by gcongr
    _ ≤ (0.160698952177 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052483232644) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353790266)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281080226962) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12941 12941 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514264059 : ℝ) ≤ plow 12941 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.758516164725 : ℝ) ≤ √(12941 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12941 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12941 Θ 1.22 ≤ 0.011657153634 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.758516164725 := by gcongr <;> linarith
      _ ≤ (0.011657153634 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12941 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12941 12941 0.011 ≤ 0.008402772759 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12941 12941 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12941 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12941 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12941 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12941 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160698952177 + 0.011657153634 + (0.008402772759 : ℝ) *
        (1 + 2 * (0.281080226962 + 0.011657153634) / (0.560514264059 * 113.758516164725))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12941]

end BstLean.Part269.N12941

/-! The original eight local profiles supply actual 12941 moment certificates. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12941 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052483232644 ∧
    0 ≤ bN 12941 BstLean.Part154.csC (groupTheta g) ∧ bN 12941 BstLean.Part154.csC (groupTheta g) ≤ 0.001353790266 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12941 12941 0.011
      (momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12941 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12941 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12941 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229092192456 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12941 0.011
      (momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12941 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12941
/-! The actual computed-centre upper energy formula at 12941. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12941

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12941)
open BstLean.Part268 (cell12941)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084816533025
  | 2 => 0.085747537543
  | 3 => 0.086675072608
  | 4 => 0.087600178755
  | 5 => 0.088524125864
  | 6 => 0.089448448640
  | 7 => 0.090374985705
  | 8 => 0.091305922373
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12941 12941 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12941 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12941

/-! Actual upper energy certificates on all 43 source endpoints at 12941. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12941)
open BstLean.Part268 (cell12941)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12941 (gMinus 12941) (1 - (cell12941 i).lower) ≤ 1 ∧
    energyUpper 12941 (gMinus 12941) (BstLean.Part211.gPlus 12941)
      (finiteEnergy 12941 12941 0.011) (1 - (cell12941 i).lower) ≤
      (cell12941 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨10,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨11,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨12,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨13,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨14,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨15,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨16,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨17,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨18,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨19,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨20,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨21,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨22,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨23,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨24,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨25,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨26,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨27,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨28,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨29,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨30,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨31,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨32,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨33,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨34,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨35,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨36,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨37,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨38,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨39,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨40,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨41,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨42,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨43,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨44,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨45,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨46,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨47,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨48,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨49,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨50,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨51,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12941) (by norm_num)
        (q := 1 - (cell12941 ⟨52,by decide⟩).lower)
        (by norm_num [cell12941]) (by norm_num [cell12941])
      exact ⟨E.1,E.2.trans (by norm_num [cell12941])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12941

/-! Source-cell containment and simple scalar guards at 12941. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12941)
open BstLean.Part268 (cell12941)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12941 ⟨10,by decide⟩).lower ∧ (cell12941 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12941 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12941 ⟨11,by decide⟩).lower ∧ (cell12941 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12941 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12941 ⟨12,by decide⟩).lower ∧ (cell12941 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12941 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12941 ⟨13,by decide⟩).lower ∧ (cell12941 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12941 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12941 ⟨14,by decide⟩).lower ∧ (cell12941 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12941 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12941 ⟨15,by decide⟩).lower ∧ (cell12941 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12941 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12941 ⟨16,by decide⟩).lower ∧ (cell12941 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12941 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12941 ⟨17,by decide⟩).lower ∧ (cell12941 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12941 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12941 ⟨18,by decide⟩).lower ∧ (cell12941 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12941 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12941 ⟨19,by decide⟩).lower ∧ (cell12941 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12941 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12941 ⟨20,by decide⟩).lower ∧ (cell12941 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12941 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12941 ⟨21,by decide⟩).lower ∧ (cell12941 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12941 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12941 ⟨22,by decide⟩).lower ∧ (cell12941 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12941 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12941 ⟨23,by decide⟩).lower ∧ (cell12941 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12941 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12941 ⟨24,by decide⟩).lower ∧ (cell12941 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12941 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12941 ⟨25,by decide⟩).lower ∧ (cell12941 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12941 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12941 ⟨26,by decide⟩).lower ∧ (cell12941 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12941 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12941 ⟨27,by decide⟩).lower ∧ (cell12941 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12941 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12941 ⟨28,by decide⟩).lower ∧ (cell12941 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12941 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12941 ⟨29,by decide⟩).lower ∧ (cell12941 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12941 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12941 ⟨30,by decide⟩).lower ∧ (cell12941 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12941 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12941 ⟨31,by decide⟩).lower ∧ (cell12941 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12941 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12941 ⟨32,by decide⟩).lower ∧ (cell12941 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12941 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12941 ⟨33,by decide⟩).lower ∧ (cell12941 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12941 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12941 ⟨34,by decide⟩).lower ∧ (cell12941 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12941 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12941 ⟨35,by decide⟩).lower ∧ (cell12941 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12941 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12941 ⟨36,by decide⟩).lower ∧ (cell12941 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12941 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12941 ⟨37,by decide⟩).lower ∧ (cell12941 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12941 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12941 ⟨38,by decide⟩).lower ∧ (cell12941 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12941 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12941 ⟨39,by decide⟩).lower ∧ (cell12941 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12941 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12941 ⟨40,by decide⟩).lower ∧ (cell12941 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12941 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12941 ⟨41,by decide⟩).lower ∧ (cell12941 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12941 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12941 ⟨42,by decide⟩).lower ∧ (cell12941 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12941 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12941 ⟨43,by decide⟩).lower ∧ (cell12941 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12941 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12941 ⟨44,by decide⟩).lower ∧ (cell12941 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12941 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12941 ⟨45,by decide⟩).lower ∧ (cell12941 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12941 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12941 ⟨46,by decide⟩).lower ∧ (cell12941 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12941 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12941 ⟨47,by decide⟩).lower ∧ (cell12941 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12941 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12941 ⟨48,by decide⟩).lower ∧ (cell12941 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12941 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12941 ⟨49,by decide⟩).lower ∧ (cell12941 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12941 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12941 ⟨50,by decide⟩).lower ∧ (cell12941 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12941 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12941 ⟨51,by decide⟩).lower ∧ (cell12941 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12941 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12941 ⟨52,by decide⟩).lower ∧ (cell12941 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12941 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12941 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12941 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12941,cell12941,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12941 i).lower ∧
    (cell12941 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12941 i).upper ≤ (0.532 : ℝ) ∧
    (cell12941 i).centre ≤ (0.1 : ℝ) ∧ (cell12941 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12941 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12941 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12941

/-! The local source numeric instances at 12941 have no network premises. -/
namespace BstLean.Part269.N12941
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12941)
open BstLean.Part268 (cell12941)

noncomputable def sourceNumerics12941 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12941 (cell12941 i)
      scalarRow12941.M scalarRow12941.H scalarRow12941.xi := by
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
    energy_allowance := scalarRow12941.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12941]
    centre_nonneg := (scalarRow12941.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12941])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12941
/-! Actual 12942 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12942 ≤ (1.035469915425 : ℝ) := by
  have hr : (113.762911355151 : ℝ) ≤ √(12942 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.762911355151 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12942 12942 (11 / 1000) ≤
    (0.008402448118 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12942) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.762911355151 : ℝ) ≤ √(12942 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12942)
  have hdiv : K / √(12942 : ℝ) ≤ K / 113.762911355151 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.762911355151 ≤ (0.008402448118 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12942.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12942 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12942 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12942 := gPlus_lower 12942
end BstLean.Part269.N12942

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12942
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035469915424 : ℝ) ≤ wn 12942 := by
  have hn : √(12942 : ℝ) ≤ 113.762911355152 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12942 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.762911355152 ≤ 2 / √(12942 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247090029 : ℝ) ≤ rhoBar 12942 BstLean.Part154.csC ∧
    rhoBar 12942 BstLean.Part154.csC ≤ 0.000247090412 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035469915424 : ℝ) / (1.295212 * 12942) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035469915425 : ℝ) / (1.29521 * 12942) := by gcongr
      _ ≤ (0.000247090412 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12942 BstLean.Part154.csC) ≤ 0.000988422702 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12942 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) ≤ 0.000188729157 ∧
    cc1 (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) ≤ 0.000120089650 ∧
    cc2 (rhoBar 12942 BstLean.Part154.csC) ≤ 0.000069713004 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12942 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12942 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12942 BstLean.Part154.csC * nuR (rhoBar 12942 BstLean.Part154.csC)) ≤ 0.000494196088 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247090412 : ℝ) * 0.000988422702 := by gcongr
      _ ≤ (0.000494196088 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12942 BstLean.Part154.csC) * nuR (rhoBar 12942 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988422702 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12942 BstLean.Part154.csC) * rhoBar 12942 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247090412 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247090412 / 2 + 0.399 * 0.000988422702 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188729157 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494196088 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120089650 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247090412 / 1.414213562 := by gcongr
      _ ≤ (0.000069713004 : ℝ) := by norm_num

end BstLean.Part269.N12942

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12942
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) ≤ 1.53820E-7 := by
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12942 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12942 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12942 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188729157 : ℝ) ^ 2 + 0.000120089650 ^ 2 + 3 * 0.000069713004 ^ 2 +
        2 * 0.797885 * 0.000188729157 * 0.000120089650 + 2 * 0.000188729157 * 0.000069713004 +
        4 * 0.797885 * 0.000120089650 * 0.000069713004 := by gcongr
    _ ≤ (1.53820E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12942 BstLean.Part154.csC Θ ≤ 0.002578428325 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12942 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12942 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12942 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035469915425 * 1.53820E-7 / (0.000247090029 : ℝ) := by gcongr
    _ ≤ 0.002578428325 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12942 BstLean.Part154.csC Θ ≤ 0.002859971426 + 0.000651528749 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12942 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12942 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035469915425 : ℝ) * ((2 * Θ * 0.000247090412 +
        (6863 / 10000) * 0.000247090412 * 12942 * 0.000988422702) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002859971426 + 0.000651528749 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12942 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12942 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12942 0.011 Θ ∧ gammaRatio 12942 0.011 Θ ≤ 0.000084943294 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12942 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035469915425 : ℝ) * 0.525 / ((1 - 0.011) * 12942) := by gcongr
      _ ≤ (0.000084943294 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12942 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12942 0.011 Θ) :=
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
    badAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12942 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12942 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12942 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12942 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12942 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12942 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12942 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12942 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12942 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12942 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035469915425 : ℝ) * 12942 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003280529982 + 0.003229957074 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12942

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12942
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12942 BstLean.Part154.csC) (piBar (rhoBar 12942 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12942 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12942 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12942 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12942 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12942 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12942 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12942 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12942 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12942 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12942 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051986004388 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12942) ≤ 0.010497600377 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12942 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035469915425)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010497600377 + 2 * 0.737676 / 12942) := by gcongr
    _ ≤ (0.051986004388 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12942 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12942

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12942
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514307610 : ℝ) ≤ plow 12942 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12942) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482857446)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353674871) : eMP 12942 0.011 xi bn ≤ 0.001165706359 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12942 : ℝ) * (1 - 0.011))) ≤ 0.000576412381 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353674871 / (12942 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576412381 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576412381 : ℝ) + 3.141593 * 0.052482857446 / (12942 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165706359 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482857446)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353674871) : PiBarMP 12942 12 0.011 xi bn ≤ 0.159721046976 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12942 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036792320816 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.135485149443 : ℝ) ≤ √((12942 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.762911355151 : ℝ) ≤ √(12942 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12942) ≤ 0.122468809007 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036792320816 + 0.052482857446 * 1.772454 / (2 * (113.135485149443 : ℝ))) * (1 + 0.001165706359) +
        8 / (12942 * 113.762911355151) + 0.122468809007 := by gcongr
    _ ≤ (0.159721046976 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482857446)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353674871) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281077377962) :
    parallelOracle 12942 0.011 xi bn cd ≤ 0.160692559786 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12942 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12942 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514307610 : ℝ) ≤ plow 12942 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.762911355151 : ℝ) ≤ √(12942 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281077377962 : ℝ) / (2 * 0.560514307610 * 113.762911355151)) * 0.159721046976 +
        0.281077377962 ^ 2 / (2 * 0.560514307610 * 113.762911355151) := by gcongr
    _ ≤ (0.160692559786 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482857446) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353674871)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281077377962) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12942 12942 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514307610 : ℝ) ≤ plow 12942 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.762911355151 : ℝ) ≤ √(12942 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12942 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12942 Θ 1.22 ≤ 0.011656703263 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.762911355151 := by gcongr <;> linarith
      _ ≤ (0.011656703263 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12942 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12942 12942 0.011 ≤ 0.008402448118 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12942 12942 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12942 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12942 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12942 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12942 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160692559786 + 0.011656703263 + (0.008402448118 : ℝ) *
        (1 + 2 * (0.281077377962 + 0.011656703263) / (0.560514307610 * 113.762911355151))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12942]

end BstLean.Part269.N12942

/-! The original eight local profiles supply actual 12942 moment certificates. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12942 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052482857446 ∧
    0 ≤ bN 12942 BstLean.Part154.csC (groupTheta g) ∧ bN 12942 BstLean.Part154.csC (groupTheta g) ≤ 0.001353674871 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12942 12942 0.011
      (momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12942 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12942 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12942 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229091373574 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12942 0.011
      (momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12942 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12942
/-! The actual computed-centre upper energy formula at 12942. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12942

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12942)
open BstLean.Part268 (cell12942)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084813849558
  | 2 => 0.085744809729
  | 3 => 0.086672294802
  | 4 => 0.087597343959
  | 5 => 0.088521225480
  | 6 => 0.089445472192
  | 7 => 0.090371920521
  | 8 => 0.091302753235
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12942 12942 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12942 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12942

/-! Actual upper energy certificates on all 43 source endpoints at 12942. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12942)
open BstLean.Part268 (cell12942)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12942 (gMinus 12942) (1 - (cell12942 i).lower) ≤ 1 ∧
    energyUpper 12942 (gMinus 12942) (BstLean.Part211.gPlus 12942)
      (finiteEnergy 12942 12942 0.011) (1 - (cell12942 i).lower) ≤
      (cell12942 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨10,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨11,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨12,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨13,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨14,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨15,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨16,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨17,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨18,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨19,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨20,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨21,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨22,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨23,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨24,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨25,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨26,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨27,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨28,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨29,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨30,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨31,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨32,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨33,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨34,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨35,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨36,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨37,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨38,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨39,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨40,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨41,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨42,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨43,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨44,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨45,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨46,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨47,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨48,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨49,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨50,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨51,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12942) (by norm_num)
        (q := 1 - (cell12942 ⟨52,by decide⟩).lower)
        (by norm_num [cell12942]) (by norm_num [cell12942])
      exact ⟨E.1,E.2.trans (by norm_num [cell12942])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12942

/-! Source-cell containment and simple scalar guards at 12942. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12942)
open BstLean.Part268 (cell12942)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12942 ⟨10,by decide⟩).lower ∧ (cell12942 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12942 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12942 ⟨11,by decide⟩).lower ∧ (cell12942 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12942 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12942 ⟨12,by decide⟩).lower ∧ (cell12942 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12942 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12942 ⟨13,by decide⟩).lower ∧ (cell12942 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12942 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12942 ⟨14,by decide⟩).lower ∧ (cell12942 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12942 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12942 ⟨15,by decide⟩).lower ∧ (cell12942 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12942 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12942 ⟨16,by decide⟩).lower ∧ (cell12942 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12942 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12942 ⟨17,by decide⟩).lower ∧ (cell12942 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12942 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12942 ⟨18,by decide⟩).lower ∧ (cell12942 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12942 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12942 ⟨19,by decide⟩).lower ∧ (cell12942 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12942 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12942 ⟨20,by decide⟩).lower ∧ (cell12942 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12942 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12942 ⟨21,by decide⟩).lower ∧ (cell12942 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12942 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12942 ⟨22,by decide⟩).lower ∧ (cell12942 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12942 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12942 ⟨23,by decide⟩).lower ∧ (cell12942 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12942 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12942 ⟨24,by decide⟩).lower ∧ (cell12942 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12942 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12942 ⟨25,by decide⟩).lower ∧ (cell12942 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12942 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12942 ⟨26,by decide⟩).lower ∧ (cell12942 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12942 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12942 ⟨27,by decide⟩).lower ∧ (cell12942 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12942 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12942 ⟨28,by decide⟩).lower ∧ (cell12942 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12942 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12942 ⟨29,by decide⟩).lower ∧ (cell12942 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12942 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12942 ⟨30,by decide⟩).lower ∧ (cell12942 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12942 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12942 ⟨31,by decide⟩).lower ∧ (cell12942 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12942 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12942 ⟨32,by decide⟩).lower ∧ (cell12942 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12942 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12942 ⟨33,by decide⟩).lower ∧ (cell12942 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12942 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12942 ⟨34,by decide⟩).lower ∧ (cell12942 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12942 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12942 ⟨35,by decide⟩).lower ∧ (cell12942 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12942 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12942 ⟨36,by decide⟩).lower ∧ (cell12942 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12942 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12942 ⟨37,by decide⟩).lower ∧ (cell12942 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12942 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12942 ⟨38,by decide⟩).lower ∧ (cell12942 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12942 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12942 ⟨39,by decide⟩).lower ∧ (cell12942 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12942 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12942 ⟨40,by decide⟩).lower ∧ (cell12942 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12942 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12942 ⟨41,by decide⟩).lower ∧ (cell12942 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12942 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12942 ⟨42,by decide⟩).lower ∧ (cell12942 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12942 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12942 ⟨43,by decide⟩).lower ∧ (cell12942 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12942 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12942 ⟨44,by decide⟩).lower ∧ (cell12942 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12942 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12942 ⟨45,by decide⟩).lower ∧ (cell12942 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12942 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12942 ⟨46,by decide⟩).lower ∧ (cell12942 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12942 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12942 ⟨47,by decide⟩).lower ∧ (cell12942 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12942 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12942 ⟨48,by decide⟩).lower ∧ (cell12942 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12942 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12942 ⟨49,by decide⟩).lower ∧ (cell12942 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12942 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12942 ⟨50,by decide⟩).lower ∧ (cell12942 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12942 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12942 ⟨51,by decide⟩).lower ∧ (cell12942 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12942 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12942 ⟨52,by decide⟩).lower ∧ (cell12942 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12942 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12942 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12942 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12942,cell12942,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12942 i).lower ∧
    (cell12942 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12942 i).upper ≤ (0.532 : ℝ) ∧
    (cell12942 i).centre ≤ (0.1 : ℝ) ∧ (cell12942 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12942 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12942 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12942

/-! The local source numeric instances at 12942 have no network premises. -/
namespace BstLean.Part269.N12942
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12942)
open BstLean.Part268 (cell12942)

noncomputable def sourceNumerics12942 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12942 (cell12942 i)
      scalarRow12942.M scalarRow12942.H scalarRow12942.xi := by
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
    energy_allowance := scalarRow12942.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12942]
    centre_nonneg := (scalarRow12942.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12942])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12942
/-! Actual 12943 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12943 ≤ (1.035468533223 : ℝ) := by
  have hr : (113.767306375777 : ℝ) ≤ √(12943 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.767306375777 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12943 12943 (11 / 1000) ≤
    (0.008402123515 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12943) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.767306375777 : ℝ) ≤ √(12943 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12943)
  have hdiv : K / √(12943 : ℝ) ≤ K / 113.767306375777 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.767306375777 ≤ (0.008402123515 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12943.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12943 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12943 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12943 := gPlus_lower 12943
end BstLean.Part269.N12943

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12943
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035468533222 : ℝ) ≤ wn 12943 := by
  have hn : √(12943 : ℝ) ≤ 113.767306375778 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12943 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.767306375778 ≤ 2 / √(12943 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247070609 : ℝ) ≤ rhoBar 12943 BstLean.Part154.csC ∧
    rhoBar 12943 BstLean.Part154.csC ≤ 0.000247070991 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035468533222 : ℝ) / (1.295212 * 12943) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035468533223 : ℝ) / (1.29521 * 12943) := by gcongr
      _ ≤ (0.000247070991 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12943 BstLean.Part154.csC) ≤ 0.000988345009 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12943 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) ≤ 0.000188714322 ∧
    cc1 (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) ≤ 0.000120080211 ∧
    cc2 (rhoBar 12943 BstLean.Part154.csC) ≤ 0.000069707524 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12943 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12943 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12943 BstLean.Part154.csC * nuR (rhoBar 12943 BstLean.Part154.csC)) ≤ 0.000494157244 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247070991 : ℝ) * 0.000988345009 := by gcongr
      _ ≤ (0.000494157244 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12943 BstLean.Part154.csC) * nuR (rhoBar 12943 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988345009 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12943 BstLean.Part154.csC) * rhoBar 12943 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247070991 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247070991 / 2 + 0.399 * 0.000988345009 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188714322 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494157244 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120080211 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247070991 / 1.414213562 := by gcongr
      _ ≤ (0.000069707524 : ℝ) := by norm_num

end BstLean.Part269.N12943

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12943
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) ≤ 1.53796E-7 := by
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12943 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12943 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12943 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188714322 : ℝ) ^ 2 + 0.000120080211 ^ 2 + 3 * 0.000069707524 ^ 2 +
        2 * 0.797885 * 0.000188714322 * 0.000120080211 + 2 * 0.000188714322 * 0.000069707524 +
        4 * 0.797885 * 0.000120080211 * 0.000069707524 := by gcongr
    _ ≤ (1.53796E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12943 BstLean.Part154.csC Θ ≤ 0.002578225216 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12943 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12943 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12943 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035468533223 * 1.53796E-7 / (0.000247070609 : ℝ) := by gcongr
    _ ≤ 0.002578225216 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12943 BstLean.Part154.csC Θ ≤ 0.002859738982 + 0.000651476670 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12943 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12943 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035468533223 : ℝ) * ((2 * Θ * 0.000247070991 +
        (6863 / 10000) * 0.000247070991 * 12943 * 0.000988345009) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002859738982 + 0.000651476670 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12943 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12943 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12943 0.011 Θ ∧ gammaRatio 12943 0.011 Θ ≤ 0.000084936618 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12943 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035468533223 : ℝ) * 0.525 / ((1 - 0.011) * 12943) := by gcongr
      _ ≤ (0.000084936618 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12943 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12943 0.011 Θ) :=
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
    badAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12943 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12943 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12943 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12943 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12943 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12943 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12943 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12943 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12943 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12943 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035468533223 : ℝ) * 12943 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003280297538 + 0.003229701886 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12943

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12943
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12943 BstLean.Part154.csC) (piBar (rhoBar 12943 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12943 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12943 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12943 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12943 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12943 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12943 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12943 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12943 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12943 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12943 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051983974507 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12943) ≤ 0.010497194837 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12943 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035468533223)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010497194837 + 2 * 0.737676 / 12943) := by gcongr
    _ ≤ (0.051983974507 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12943 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12943

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12943
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514351155 : ℝ) ≤ plow 12943 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12943) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482491029)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353568239) : eMP 12943 0.011 xi bn ≤ 0.001165615334 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12943 : ℝ) * (1 - 0.011))) ≤ 0.000576367411 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353568239 / (12943 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576367411 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576367411 : ℝ) + 3.141593 * 0.052482491029 / (12943 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165615334 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482491029)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353568239) : PiBarMP 12943 12 0.011 xi bn ≤ 0.159714842188 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12943 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036790871681 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.139855930613 : ℝ) ≤ √((12943 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.767306375777 : ℝ) ≤ √(12943 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12943) ≤ 0.122464077833 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036790871681 + 0.052482491029 * 1.772454 / (2 * (113.139855930613 : ℝ))) * (1 + 0.001165615334) +
        8 / (12943 * 113.767306375777) + 0.122464077833 := by gcongr
    _ ≤ (0.159714842188 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482491029)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353568239) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281074548362) :
    parallelOracle 12943 0.011 xi bn cd ≤ 0.160686287701 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12943 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12943 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514351155 : ℝ) ≤ plow 12943 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.767306375777 : ℝ) ≤ √(12943 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281074548362 : ℝ) / (2 * 0.560514351155 * 113.767306375777)) * 0.159714842188 +
        0.281074548362 ^ 2 / (2 * 0.560514351155 * 113.767306375777) := by gcongr
    _ ≤ (0.160686287701 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482491029) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353568239)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281074548362) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12943 12943 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514351155 : ℝ) ≤ plow 12943 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.767306375777 : ℝ) ≤ √(12943 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12943 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12943 Θ 1.22 ≤ 0.011656252946 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.767306375777 := by gcongr <;> linarith
      _ ≤ (0.011656252946 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12943 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12943 12943 0.011 ≤ 0.008402123515 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12943 12943 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12943 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12943 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12943 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12943 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160686287701 + 0.011656252946 + (0.008402123515 : ℝ) *
        (1 + 2 * (0.281074548362 + 0.011656252946) / (0.560514351155 * 113.767306375777))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12943]

end BstLean.Part269.N12943

/-! The original eight local profiles supply actual 12943 moment certificates. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12943 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052482491029 ∧
    0 ≤ bN 12943 BstLean.Part154.csC (groupTheta g) ∧ bN 12943 BstLean.Part154.csC (groupTheta g) ≤ 0.001353568239 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12943 12943 0.011
      (momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12943 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12943 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12943 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229090573855 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12943 0.011
      (momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12943 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12943
/-! The actual computed-centre upper energy formula at 12943. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12943

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12943)
open BstLean.Part268 (cell12943)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084811166948
  | 2 => 0.085742082804
  | 3 => 0.086669517924
  | 4 => 0.087594510140
  | 5 => 0.088518326135
  | 6 => 0.089442496857
  | 7 => 0.090368856539
  | 8 => 0.091299585408
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12943 12943 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12943 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12943

/-! Actual upper energy certificates on all 43 source endpoints at 12943. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12943)
open BstLean.Part268 (cell12943)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12943 (gMinus 12943) (1 - (cell12943 i).lower) ≤ 1 ∧
    energyUpper 12943 (gMinus 12943) (BstLean.Part211.gPlus 12943)
      (finiteEnergy 12943 12943 0.011) (1 - (cell12943 i).lower) ≤
      (cell12943 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨10,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨11,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨12,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨13,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨14,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨15,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨16,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨17,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨18,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨19,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨20,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨21,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨22,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨23,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨24,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨25,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨26,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨27,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨28,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨29,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨30,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨31,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨32,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨33,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨34,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨35,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨36,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨37,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨38,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨39,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨40,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨41,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨42,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨43,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨44,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨45,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨46,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨47,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨48,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨49,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨50,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨51,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12943) (by norm_num)
        (q := 1 - (cell12943 ⟨52,by decide⟩).lower)
        (by norm_num [cell12943]) (by norm_num [cell12943])
      exact ⟨E.1,E.2.trans (by norm_num [cell12943])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12943

/-! Source-cell containment and simple scalar guards at 12943. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12943)
open BstLean.Part268 (cell12943)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12943 ⟨10,by decide⟩).lower ∧ (cell12943 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12943 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12943 ⟨11,by decide⟩).lower ∧ (cell12943 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12943 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12943 ⟨12,by decide⟩).lower ∧ (cell12943 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12943 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12943 ⟨13,by decide⟩).lower ∧ (cell12943 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12943 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12943 ⟨14,by decide⟩).lower ∧ (cell12943 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12943 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12943 ⟨15,by decide⟩).lower ∧ (cell12943 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12943 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12943 ⟨16,by decide⟩).lower ∧ (cell12943 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12943 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12943 ⟨17,by decide⟩).lower ∧ (cell12943 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12943 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12943 ⟨18,by decide⟩).lower ∧ (cell12943 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12943 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12943 ⟨19,by decide⟩).lower ∧ (cell12943 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12943 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12943 ⟨20,by decide⟩).lower ∧ (cell12943 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12943 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12943 ⟨21,by decide⟩).lower ∧ (cell12943 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12943 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12943 ⟨22,by decide⟩).lower ∧ (cell12943 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12943 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12943 ⟨23,by decide⟩).lower ∧ (cell12943 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12943 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12943 ⟨24,by decide⟩).lower ∧ (cell12943 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12943 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12943 ⟨25,by decide⟩).lower ∧ (cell12943 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12943 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12943 ⟨26,by decide⟩).lower ∧ (cell12943 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12943 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12943 ⟨27,by decide⟩).lower ∧ (cell12943 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12943 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12943 ⟨28,by decide⟩).lower ∧ (cell12943 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12943 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12943 ⟨29,by decide⟩).lower ∧ (cell12943 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12943 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12943 ⟨30,by decide⟩).lower ∧ (cell12943 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12943 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12943 ⟨31,by decide⟩).lower ∧ (cell12943 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12943 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12943 ⟨32,by decide⟩).lower ∧ (cell12943 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12943 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12943 ⟨33,by decide⟩).lower ∧ (cell12943 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12943 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12943 ⟨34,by decide⟩).lower ∧ (cell12943 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12943 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12943 ⟨35,by decide⟩).lower ∧ (cell12943 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12943 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12943 ⟨36,by decide⟩).lower ∧ (cell12943 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12943 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12943 ⟨37,by decide⟩).lower ∧ (cell12943 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12943 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12943 ⟨38,by decide⟩).lower ∧ (cell12943 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12943 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12943 ⟨39,by decide⟩).lower ∧ (cell12943 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12943 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12943 ⟨40,by decide⟩).lower ∧ (cell12943 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12943 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12943 ⟨41,by decide⟩).lower ∧ (cell12943 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12943 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12943 ⟨42,by decide⟩).lower ∧ (cell12943 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12943 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12943 ⟨43,by decide⟩).lower ∧ (cell12943 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12943 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12943 ⟨44,by decide⟩).lower ∧ (cell12943 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12943 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12943 ⟨45,by decide⟩).lower ∧ (cell12943 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12943 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12943 ⟨46,by decide⟩).lower ∧ (cell12943 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12943 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12943 ⟨47,by decide⟩).lower ∧ (cell12943 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12943 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12943 ⟨48,by decide⟩).lower ∧ (cell12943 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12943 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12943 ⟨49,by decide⟩).lower ∧ (cell12943 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12943 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12943 ⟨50,by decide⟩).lower ∧ (cell12943 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12943 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12943 ⟨51,by decide⟩).lower ∧ (cell12943 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12943 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12943 ⟨52,by decide⟩).lower ∧ (cell12943 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12943 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12943 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12943 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12943,cell12943,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12943 i).lower ∧
    (cell12943 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12943 i).upper ≤ (0.532 : ℝ) ∧
    (cell12943 i).centre ≤ (0.1 : ℝ) ∧ (cell12943 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12943 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12943 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12943

/-! The local source numeric instances at 12943 have no network premises. -/
namespace BstLean.Part269.N12943
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12943)
open BstLean.Part268 (cell12943)

noncomputable def sourceNumerics12943 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12943 (cell12943 i)
      scalarRow12943.M scalarRow12943.H scalarRow12943.xi := by
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
    energy_allowance := scalarRow12943.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12943]
    centre_nonneg := (scalarRow12943.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12943])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12943
/-! Actual 12944 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12944 ≤ (1.035467151183 : ℝ) := by
  have hr : (113.771701226623 : ℝ) ≤ √(12944 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.771701226623 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12944 12944 (11 / 1000) ≤
    (0.008401798949 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12944) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.771701226623 : ℝ) ≤ √(12944 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12944)
  have hdiv : K / √(12944 : ℝ) ≤ K / 113.771701226623 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.771701226623 ≤ (0.008401798949 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12944.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12944 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12944 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12944 := gPlus_lower 12944
end BstLean.Part269.N12944

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12944
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035467151182 : ℝ) ≤ wn 12944 := by
  have hn : √(12944 : ℝ) ≤ 113.771701226624 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12944 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.771701226624 ≤ 2 / √(12944 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247051191 : ℝ) ≤ rhoBar 12944 BstLean.Part154.csC ∧
    rhoBar 12944 BstLean.Part154.csC ≤ 0.000247051574 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035467151182 : ℝ) / (1.295212 * 12944) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035467151183 : ℝ) / (1.29521 * 12944) := by gcongr
      _ ≤ (0.000247051574 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12944 BstLean.Part154.csC) ≤ 0.000988267331 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12944 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) ≤ 0.000188699491 ∧
    cc1 (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) ≤ 0.000120070773 ∧
    cc2 (rhoBar 12944 BstLean.Part154.csC) ≤ 0.000069702046 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12944 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12944 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12944 BstLean.Part154.csC * nuR (rhoBar 12944 BstLean.Part154.csC)) ≤ 0.000494118407 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247051574 : ℝ) * 0.000988267331 := by gcongr
      _ ≤ (0.000494118407 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12944 BstLean.Part154.csC) * nuR (rhoBar 12944 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988267331 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12944 BstLean.Part154.csC) * rhoBar 12944 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247051574 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247051574 / 2 + 0.399 * 0.000988267331 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188699491 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494118407 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120070773 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247051574 / 1.414213562 := by gcongr
      _ ≤ (0.000069702046 : ℝ) := by norm_num

end BstLean.Part269.N12944

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12944
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) ≤ 1.53772E-7 := by
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12944 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12944 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12944 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188699491 : ℝ) ^ 2 + 0.000120070773 ^ 2 + 3 * 0.000069702046 ^ 2 +
        2 * 0.797885 * 0.000188699491 * 0.000120070773 + 2 * 0.000188699491 * 0.000069702046 +
        4 * 0.797885 * 0.000120070773 * 0.000069702046 := by gcongr
    _ ≤ (1.53772E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12944 BstLean.Part154.csC Θ ≤ 0.002578022055 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12944 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12944 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12944 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035467151183 * 1.53772E-7 / (0.000247051191 : ℝ) := by gcongr
    _ ≤ 0.002578022055 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12944 BstLean.Part154.csC Θ ≤ 0.002859506596 + 0.000651424602 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12944 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12944 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035467151183 : ℝ) * ((2 * Θ * 0.000247051574 +
        (6863 / 10000) * 0.000247051574 * 12944 * 0.000988267331) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002859506596 + 0.000651424602 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12944 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12944 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12944 0.011 Θ ∧ gammaRatio 12944 0.011 Θ ≤ 0.000084929943 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12944 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035467151183 : ℝ) * 0.525 / ((1 - 0.011) * 12944) := by gcongr
      _ ≤ (0.000084929943 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12944 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12944 0.011 Θ) :=
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
    badAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12944 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12944 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12944 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12944 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12944 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12944 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12944 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12944 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12944 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12944 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035467151183 : ℝ) * 12944 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003280065152 + 0.003229446657 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12944

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12944
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12944 BstLean.Part154.csC) (piBar (rhoBar 12944 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12944 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12944 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12944 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12944 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12944 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12944 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12944 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12944 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12944 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12944 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051981944864 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12944) ≤ 0.010496789344 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12944 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035467151183)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010496789344 + 2 * 0.737676 / 12944) := by gcongr
    _ ≤ (0.051981944864 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12944 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12944

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12944
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514394692 : ℝ) ≤ plow 12944 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12944) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482124647)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353461579) : eMP 12944 0.011 xi bn ≤ 0.001165524303 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12944 : ℝ) * (1 - 0.011))) ≤ 0.000576322438 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353461579 / (12944 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576322438 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576322438 : ℝ) + 3.141593 * 0.052482124647 / (12944 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165524303 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482124647)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353461579) : PiBarMP 12944 12 0.011 xi bn ≤ 0.159708637512 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12944 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036789422108 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.144226542939 : ℝ) ≤ √((12944 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.771701226623 : ℝ) ≤ √(12944 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12944) ≤ 0.122459347207 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036789422108 + 0.052482124647 * 1.772454 / (2 * (113.144226542939 : ℝ))) * (1 + 0.001165524303) +
        8 / (12944 * 113.771701226623) + 0.122459347207 := by gcongr
    _ ≤ (0.159708637512 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482124647)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353461579) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281071719073) :
    parallelOracle 12944 0.011 xi bn cd ≤ 0.160680015737 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12944 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12944 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514394692 : ℝ) ≤ plow 12944 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.771701226623 : ℝ) ≤ √(12944 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281071719073 : ℝ) / (2 * 0.560514394692 * 113.771701226623)) * 0.159708637512 +
        0.281071719073 ^ 2 / (2 * 0.560514394692 * 113.771701226623) := by gcongr
    _ ≤ (0.160680015737 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052482124647) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353461579)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281071719073) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12944 12944 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514394692 : ℝ) ≤ plow 12944 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.771701226623 : ℝ) ≤ √(12944 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12944 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12944 Θ 1.22 ≤ 0.011655802680 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.771701226623 := by gcongr <;> linarith
      _ ≤ (0.011655802680 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12944 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12944 12944 0.011 ≤ 0.008401798949 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12944 12944 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12944 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12944 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12944 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12944 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160680015737 + 0.011655802680 + (0.008401798949 : ℝ) *
        (1 + 2 * (0.281071719073 + 0.011655802680) / (0.560514394692 * 113.771701226623))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12944]

end BstLean.Part269.N12944

/-! The original eight local profiles supply actual 12944 moment certificates. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12944 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052482124647 ∧
    0 ≤ bN 12944 BstLean.Part154.csC (groupTheta g) ∧ bN 12944 BstLean.Part154.csC (groupTheta g) ≤ 0.001353461579 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12944 12944 0.011
      (momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12944 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12944 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12944 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229089774209 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12944 0.011
      (momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12944 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12944
/-! The actual computed-centre upper energy formula at 12944. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12944

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12944)
open BstLean.Part268 (cell12944)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084808485192
  | 2 => 0.085739356765
  | 3 => 0.086666741974
  | 4 => 0.087591677299
  | 5 => 0.088515427827
  | 6 => 0.089439522632
  | 7 => 0.090365793758
  | 8 => 0.091296418889
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12944 12944 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12944 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12944

/-! Actual upper energy certificates on all 43 source endpoints at 12944. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12944)
open BstLean.Part268 (cell12944)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12944 (gMinus 12944) (1 - (cell12944 i).lower) ≤ 1 ∧
    energyUpper 12944 (gMinus 12944) (BstLean.Part211.gPlus 12944)
      (finiteEnergy 12944 12944 0.011) (1 - (cell12944 i).lower) ≤
      (cell12944 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨10,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨11,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨12,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨13,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨14,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨15,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨16,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨17,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨18,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨19,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨20,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨21,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨22,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨23,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨24,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨25,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨26,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨27,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨28,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨29,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨30,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨31,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨32,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨33,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨34,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨35,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨36,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨37,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨38,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨39,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨40,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨41,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨42,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨43,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨44,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨45,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨46,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨47,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨48,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨49,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨50,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨51,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12944) (by norm_num)
        (q := 1 - (cell12944 ⟨52,by decide⟩).lower)
        (by norm_num [cell12944]) (by norm_num [cell12944])
      exact ⟨E.1,E.2.trans (by norm_num [cell12944])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12944

/-! Source-cell containment and simple scalar guards at 12944. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12944)
open BstLean.Part268 (cell12944)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12944 ⟨10,by decide⟩).lower ∧ (cell12944 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12944 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12944 ⟨11,by decide⟩).lower ∧ (cell12944 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12944 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12944 ⟨12,by decide⟩).lower ∧ (cell12944 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12944 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12944 ⟨13,by decide⟩).lower ∧ (cell12944 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12944 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12944 ⟨14,by decide⟩).lower ∧ (cell12944 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12944 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12944 ⟨15,by decide⟩).lower ∧ (cell12944 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12944 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12944 ⟨16,by decide⟩).lower ∧ (cell12944 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12944 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12944 ⟨17,by decide⟩).lower ∧ (cell12944 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12944 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12944 ⟨18,by decide⟩).lower ∧ (cell12944 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12944 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12944 ⟨19,by decide⟩).lower ∧ (cell12944 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12944 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12944 ⟨20,by decide⟩).lower ∧ (cell12944 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12944 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12944 ⟨21,by decide⟩).lower ∧ (cell12944 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12944 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12944 ⟨22,by decide⟩).lower ∧ (cell12944 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12944 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12944 ⟨23,by decide⟩).lower ∧ (cell12944 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12944 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12944 ⟨24,by decide⟩).lower ∧ (cell12944 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12944 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12944 ⟨25,by decide⟩).lower ∧ (cell12944 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12944 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12944 ⟨26,by decide⟩).lower ∧ (cell12944 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12944 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12944 ⟨27,by decide⟩).lower ∧ (cell12944 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12944 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12944 ⟨28,by decide⟩).lower ∧ (cell12944 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12944 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12944 ⟨29,by decide⟩).lower ∧ (cell12944 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12944 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12944 ⟨30,by decide⟩).lower ∧ (cell12944 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12944 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12944 ⟨31,by decide⟩).lower ∧ (cell12944 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12944 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12944 ⟨32,by decide⟩).lower ∧ (cell12944 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12944 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12944 ⟨33,by decide⟩).lower ∧ (cell12944 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12944 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12944 ⟨34,by decide⟩).lower ∧ (cell12944 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12944 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12944 ⟨35,by decide⟩).lower ∧ (cell12944 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12944 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12944 ⟨36,by decide⟩).lower ∧ (cell12944 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12944 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12944 ⟨37,by decide⟩).lower ∧ (cell12944 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12944 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12944 ⟨38,by decide⟩).lower ∧ (cell12944 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12944 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12944 ⟨39,by decide⟩).lower ∧ (cell12944 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12944 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12944 ⟨40,by decide⟩).lower ∧ (cell12944 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12944 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12944 ⟨41,by decide⟩).lower ∧ (cell12944 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12944 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12944 ⟨42,by decide⟩).lower ∧ (cell12944 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12944 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12944 ⟨43,by decide⟩).lower ∧ (cell12944 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12944 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12944 ⟨44,by decide⟩).lower ∧ (cell12944 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12944 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12944 ⟨45,by decide⟩).lower ∧ (cell12944 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12944 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12944 ⟨46,by decide⟩).lower ∧ (cell12944 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12944 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12944 ⟨47,by decide⟩).lower ∧ (cell12944 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12944 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12944 ⟨48,by decide⟩).lower ∧ (cell12944 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12944 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12944 ⟨49,by decide⟩).lower ∧ (cell12944 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12944 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12944 ⟨50,by decide⟩).lower ∧ (cell12944 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12944 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12944 ⟨51,by decide⟩).lower ∧ (cell12944 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12944 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12944 ⟨52,by decide⟩).lower ∧ (cell12944 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12944 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12944 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12944 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12944,cell12944,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12944 i).lower ∧
    (cell12944 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12944 i).upper ≤ (0.532 : ℝ) ∧
    (cell12944 i).centre ≤ (0.1 : ℝ) ∧ (cell12944 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12944 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12944 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12944

/-! The local source numeric instances at 12944 have no network premises. -/
namespace BstLean.Part269.N12944
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12944)
open BstLean.Part268 (cell12944)

noncomputable def sourceNumerics12944 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12944 (cell12944 i)
      scalarRow12944.M scalarRow12944.H scalarRow12944.xi := by
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
    energy_allowance := scalarRow12944.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12944]
    centre_nonneg := (scalarRow12944.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12944])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12944
/-! Actual 12945 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12945 ≤ (1.035465769304 : ℝ) := by
  have hr : (113.776095907708 : ℝ) ≤ √(12945 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.776095907708 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12945 12945 (11 / 1000) ≤
    (0.008401474422 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12945) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.776095907708 : ℝ) ≤ √(12945 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12945)
  have hdiv : K / √(12945 : ℝ) ≤ K / 113.776095907708 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.776095907708 ≤ (0.008401474422 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12945.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12945 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12945 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12945 := gPlus_lower 12945
end BstLean.Part269.N12945

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12945
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035465769303 : ℝ) ≤ wn 12945 := by
  have hn : √(12945 : ℝ) ≤ 113.776095907709 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12945 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.776095907709 ≤ 2 / √(12945 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247031777 : ℝ) ≤ rhoBar 12945 BstLean.Part154.csC ∧
    rhoBar 12945 BstLean.Part154.csC ≤ 0.000247032160 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035465769303 : ℝ) / (1.295212 * 12945) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035465769304 : ℝ) / (1.29521 * 12945) := by gcongr
      _ ≤ (0.000247032160 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12945 BstLean.Part154.csC) ≤ 0.000988189665 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12945 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) ≤ 0.000188684661 ∧
    cc1 (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) ≤ 0.000120061338 ∧
    cc2 (rhoBar 12945 BstLean.Part154.csC) ≤ 0.000069696569 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12945 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12945 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12945 BstLean.Part154.csC * nuR (rhoBar 12945 BstLean.Part154.csC)) ≤ 0.000494079577 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247032160 : ℝ) * 0.000988189665 := by gcongr
      _ ≤ (0.000494079577 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12945 BstLean.Part154.csC) * nuR (rhoBar 12945 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988189665 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12945 BstLean.Part154.csC) * rhoBar 12945 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247032160 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247032160 / 2 + 0.399 * 0.000988189665 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188684661 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494079577 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120061338 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247032160 / 1.414213562 := by gcongr
      _ ≤ (0.000069696569 : ℝ) := by norm_num

end BstLean.Part269.N12945

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12945
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) ≤ 1.53748E-7 := by
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12945 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12945 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12945 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188684661 : ℝ) ^ 2 + 0.000120061338 ^ 2 + 3 * 0.000069696569 ^ 2 +
        2 * 0.797885 * 0.000188684661 * 0.000120061338 + 2 * 0.000188684661 * 0.000069696569 +
        4 * 0.797885 * 0.000120061338 * 0.000069696569 := by gcongr
    _ ≤ (1.53748E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12945 BstLean.Part154.csC Θ ≤ 0.002577818823 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12945 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12945 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12945 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035465769304 * 1.53748E-7 / (0.000247031777 : ℝ) := by gcongr
    _ ≤ 0.002577818823 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12945 BstLean.Part154.csC Θ ≤ 0.002859274246 + 0.000651372542 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12945 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12945 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035465769304 : ℝ) * ((2 * Θ * 0.000247032160 +
        (6863 / 10000) * 0.000247032160 * 12945 * 0.000988189665) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002859274246 + 0.000651372542 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12945 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12945 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12945 0.011 Θ ∧ gammaRatio 12945 0.011 Θ ≤ 0.000084923269 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12945 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035465769304 : ℝ) * 0.525 / ((1 - 0.011) * 12945) := by gcongr
      _ ≤ (0.000084923269 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12945 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12945 0.011 Θ) :=
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
    badAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12945 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12945 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12945 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12945 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12945 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12945 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12945 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12945 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12945 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12945 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035465769304 : ℝ) * 12945 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279832802 + 0.003229191365 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12945

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12945
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12945 BstLean.Part154.csC) (piBar (rhoBar 12945 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12945 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12945 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12945 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12945 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12945 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12945 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12945 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12945 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12945 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12945 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051979915457 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12945) ≤ 0.010496383898 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12945 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035465769304)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010496383898 + 2 * 0.737676 / 12945) := by gcongr
    _ ≤ (0.051979915457 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12945 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12945

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12945
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514438223 : ℝ) ≤ plow 12945 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12945) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481758269)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353354883) : eMP 12945 0.011 xi bn ≤ 0.001165433266 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12945 : ℝ) * (1 - 0.011))) ≤ 0.000576277462 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353354883 / (12945 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576277462 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576277462 : ℝ) + 3.141593 * 0.052481758269 / (12945 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165433266 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481758269)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353354883) : PiBarMP 12945 12 0.011 xi bn ≤ 0.159702432839 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12945 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036787971989 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.148596986440 : ℝ) ≤ √((12945 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.776095907708 : ℝ) ≤ √(12945 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12945) ≤ 0.122454617129 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036787971989 + 0.052481758269 * 1.772454 / (2 * (113.148596986440 : ℝ))) * (1 + 0.001165433266) +
        8 / (12945 * 113.776095907708) + 0.122454617129 := by gcongr
    _ ≤ (0.159702432839 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481758269)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353354883) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281068890026) :
    parallelOracle 12945 0.011 xi bn cd ≤ 0.160673743785 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12945 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12945 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514438223 : ℝ) ≤ plow 12945 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.776095907708 : ℝ) ≤ √(12945 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281068890026 : ℝ) / (2 * 0.560514438223 * 113.776095907708)) * 0.159702432839 +
        0.281068890026 ^ 2 / (2 * 0.560514438223 * 113.776095907708) := by gcongr
    _ ≤ (0.160673743785 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481758269) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353354883)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281068890026) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12945 12945 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514438223 : ℝ) ≤ plow 12945 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.776095907708 : ℝ) ≤ √(12945 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12945 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12945 Θ 1.22 ≤ 0.011655352466 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.776095907708 := by gcongr <;> linarith
      _ ≤ (0.011655352466 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12945 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12945 12945 0.011 ≤ 0.008401474422 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12945 12945 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12945 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12945 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12945 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12945 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160673743785 + 0.011655352466 + (0.008401474422 : ℝ) *
        (1 + 2 * (0.281068890026 + 0.011655352466) / (0.560514438223 * 113.776095907708))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12945]

end BstLean.Part269.N12945

/-! The original eight local profiles supply actual 12945 moment certificates. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12945 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052481758269 ∧
    0 ≤ bN 12945 BstLean.Part154.csC (groupTheta g) ∧ bN 12945 BstLean.Part154.csC (groupTheta g) ≤ 0.001353354883 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12945 12945 0.011
      (momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12945 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12945 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12945 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229088974569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12945 0.011
      (momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12945 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12945
/-! The actual computed-centre upper energy formula at 12945. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12945

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12945)
open BstLean.Part268 (cell12945)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084805804290
  | 2 => 0.085736631614
  | 3 => 0.086663966950
  | 4 => 0.087588845433
  | 5 => 0.088512530556
  | 6 => 0.089436549518
  | 7 => 0.090362732177
  | 8 => 0.091293253678
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12945 12945 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12945 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12945

/-! Actual upper energy certificates on all 43 source endpoints at 12945. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12945)
open BstLean.Part268 (cell12945)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12945 (gMinus 12945) (1 - (cell12945 i).lower) ≤ 1 ∧
    energyUpper 12945 (gMinus 12945) (BstLean.Part211.gPlus 12945)
      (finiteEnergy 12945 12945 0.011) (1 - (cell12945 i).lower) ≤
      (cell12945 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨10,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨11,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨12,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨13,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨14,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨15,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨16,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨17,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨18,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨19,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨20,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨21,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨22,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨23,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨24,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨25,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨26,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨27,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨28,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨29,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨30,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨31,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨32,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨33,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨34,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨35,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨36,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨37,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨38,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨39,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨40,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨41,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨42,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨43,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨44,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨45,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨46,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨47,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨48,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨49,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨50,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨51,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12945) (by norm_num)
        (q := 1 - (cell12945 ⟨52,by decide⟩).lower)
        (by norm_num [cell12945]) (by norm_num [cell12945])
      exact ⟨E.1,E.2.trans (by norm_num [cell12945])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12945

/-! Source-cell containment and simple scalar guards at 12945. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12945)
open BstLean.Part268 (cell12945)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12945 ⟨10,by decide⟩).lower ∧ (cell12945 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12945 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12945 ⟨11,by decide⟩).lower ∧ (cell12945 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12945 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12945 ⟨12,by decide⟩).lower ∧ (cell12945 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12945 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12945 ⟨13,by decide⟩).lower ∧ (cell12945 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12945 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12945 ⟨14,by decide⟩).lower ∧ (cell12945 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12945 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12945 ⟨15,by decide⟩).lower ∧ (cell12945 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12945 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12945 ⟨16,by decide⟩).lower ∧ (cell12945 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12945 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12945 ⟨17,by decide⟩).lower ∧ (cell12945 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12945 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12945 ⟨18,by decide⟩).lower ∧ (cell12945 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12945 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12945 ⟨19,by decide⟩).lower ∧ (cell12945 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12945 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12945 ⟨20,by decide⟩).lower ∧ (cell12945 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12945 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12945 ⟨21,by decide⟩).lower ∧ (cell12945 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12945 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12945 ⟨22,by decide⟩).lower ∧ (cell12945 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12945 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12945 ⟨23,by decide⟩).lower ∧ (cell12945 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12945 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12945 ⟨24,by decide⟩).lower ∧ (cell12945 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12945 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12945 ⟨25,by decide⟩).lower ∧ (cell12945 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12945 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12945 ⟨26,by decide⟩).lower ∧ (cell12945 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12945 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12945 ⟨27,by decide⟩).lower ∧ (cell12945 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12945 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12945 ⟨28,by decide⟩).lower ∧ (cell12945 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12945 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12945 ⟨29,by decide⟩).lower ∧ (cell12945 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12945 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12945 ⟨30,by decide⟩).lower ∧ (cell12945 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12945 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12945 ⟨31,by decide⟩).lower ∧ (cell12945 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12945 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12945 ⟨32,by decide⟩).lower ∧ (cell12945 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12945 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12945 ⟨33,by decide⟩).lower ∧ (cell12945 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12945 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12945 ⟨34,by decide⟩).lower ∧ (cell12945 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12945 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12945 ⟨35,by decide⟩).lower ∧ (cell12945 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12945 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12945 ⟨36,by decide⟩).lower ∧ (cell12945 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12945 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12945 ⟨37,by decide⟩).lower ∧ (cell12945 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12945 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12945 ⟨38,by decide⟩).lower ∧ (cell12945 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12945 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12945 ⟨39,by decide⟩).lower ∧ (cell12945 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12945 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12945 ⟨40,by decide⟩).lower ∧ (cell12945 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12945 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12945 ⟨41,by decide⟩).lower ∧ (cell12945 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12945 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12945 ⟨42,by decide⟩).lower ∧ (cell12945 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12945 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12945 ⟨43,by decide⟩).lower ∧ (cell12945 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12945 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12945 ⟨44,by decide⟩).lower ∧ (cell12945 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12945 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12945 ⟨45,by decide⟩).lower ∧ (cell12945 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12945 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12945 ⟨46,by decide⟩).lower ∧ (cell12945 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12945 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12945 ⟨47,by decide⟩).lower ∧ (cell12945 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12945 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12945 ⟨48,by decide⟩).lower ∧ (cell12945 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12945 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12945 ⟨49,by decide⟩).lower ∧ (cell12945 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12945 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12945 ⟨50,by decide⟩).lower ∧ (cell12945 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12945 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12945 ⟨51,by decide⟩).lower ∧ (cell12945 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12945 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12945 ⟨52,by decide⟩).lower ∧ (cell12945 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12945 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12945 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12945 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12945,cell12945,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12945 i).lower ∧
    (cell12945 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12945 i).upper ≤ (0.532 : ℝ) ∧
    (cell12945 i).centre ≤ (0.1 : ℝ) ∧ (cell12945 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12945 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12945 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12945

/-! The local source numeric instances at 12945 have no network premises. -/
namespace BstLean.Part269.N12945
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12945)
open BstLean.Part268 (cell12945)

noncomputable def sourceNumerics12945 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12945 (cell12945 i)
      scalarRow12945.M scalarRow12945.H scalarRow12945.xi := by
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
    energy_allowance := scalarRow12945.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12945]
    centre_nonneg := (scalarRow12945.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12945])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12945
/-! Actual 12946 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12946 ≤ (1.035464387586 : ℝ) := by
  have hr : (113.780490419052 : ℝ) ≤ √(12946 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.780490419052 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12946 12946 (11 / 1000) ≤
    (0.008401149932 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12946) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.780490419052 : ℝ) ≤ √(12946 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12946)
  have hdiv : K / √(12946 : ℝ) ≤ K / 113.780490419052 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.780490419052 ≤ (0.008401149932 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12946.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12946 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12946 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12946 := gPlus_lower 12946
end BstLean.Part269.N12946

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12946
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035464387585 : ℝ) ≤ wn 12946 := by
  have hn : √(12946 : ℝ) ≤ 113.780490419053 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12946 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.780490419053 ≤ 2 / √(12946 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247012366 : ℝ) ≤ rhoBar 12946 BstLean.Part154.csC ∧
    rhoBar 12946 BstLean.Part154.csC ≤ 0.000247012748 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035464387585 : ℝ) / (1.295212 * 12946) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035464387586 : ℝ) / (1.29521 * 12946) := by gcongr
      _ ≤ (0.000247012748 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12946 BstLean.Part154.csC) ≤ 0.000988112008 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12946 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) ≤ 0.000188669834 ∧
    cc1 (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) ≤ 0.000120051903 ∧
    cc2 (rhoBar 12946 BstLean.Part154.csC) ≤ 0.000069691092 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12946 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12946 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12946 BstLean.Part154.csC * nuR (rhoBar 12946 BstLean.Part154.csC)) ≤ 0.000494040750 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247012748 : ℝ) * 0.000988112008 := by gcongr
      _ ≤ (0.000494040750 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12946 BstLean.Part154.csC) * nuR (rhoBar 12946 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988112008 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12946 BstLean.Part154.csC) * rhoBar 12946 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247012748 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247012748 / 2 + 0.399 * 0.000988112008 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188669834 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494040750 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120051903 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247012748 / 1.414213562 := by gcongr
      _ ≤ (0.000069691092 : ℝ) := by norm_num

end BstLean.Part269.N12946

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12946
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) ≤ 1.53724E-7 := by
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12946 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12946 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12946 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188669834 : ℝ) ^ 2 + 0.000120051903 ^ 2 + 3 * 0.000069691092 ^ 2 +
        2 * 0.797885 * 0.000188669834 * 0.000120051903 + 2 * 0.000188669834 * 0.000069691092 +
        4 * 0.797885 * 0.000120051903 * 0.000069691092 := by gcongr
    _ ≤ (1.53724E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12946 BstLean.Part154.csC Θ ≤ 0.002577615528 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12946 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12946 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12946 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035464387586 * 1.53724E-7 / (0.000247012366 : ℝ) := by gcongr
    _ ≤ 0.002577615528 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12946 BstLean.Part154.csC Θ ≤ 0.002859041911 + 0.000651320487 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12946 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12946 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035464387586 : ℝ) * ((2 * Θ * 0.000247012748 +
        (6863 / 10000) * 0.000247012748 * 12946 * 0.000988112008) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002859041911 + 0.000651320487 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12946 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12946 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12946 0.011 Θ ∧ gammaRatio 12946 0.011 Θ ≤ 0.000084916596 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12946 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035464387586 : ℝ) * 0.525 / ((1 - 0.011) * 12946) := by gcongr
      _ ≤ (0.000084916596 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12946 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12946 0.011 Θ) :=
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
    badAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12946 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12946 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12946 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12946 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12946 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12946 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12946 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12946 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12946 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12946 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035464387586 : ℝ) * 12946 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279600467 + 0.003228936015 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12946

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12946
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12946 BstLean.Part154.csC) (piBar (rhoBar 12946 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12946 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12946 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12946 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12946 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12946 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12946 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12946 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12946 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12946 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12946 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051977886292 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12946) ≤ 0.010495978500 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12946 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035464387586)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010495978500 + 2 * 0.737676 / 12946) := by gcongr
    _ ≤ (0.051977886292 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12946 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12946

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12946
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514481747 : ℝ) ≤ plow 12946 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12946) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481391875)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353248153) : eMP 12946 0.011 xi bn ≤ 0.001165342220 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12946 : ℝ) * (1 - 0.011))) ≤ 0.000576232481 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353248153 / (12946 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576232481 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576232481 : ℝ) + 3.141593 * 0.052481391875 / (12946 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165342220 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481391875)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353248153) : PiBarMP 12946 12 0.011 xi bn ≤ 0.159696228196 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12946 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036786521350 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.152967261137 : ℝ) ≤ √((12946 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.780490419052 : ℝ) ≤ √(12946 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12946) ≤ 0.122449887599 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036786521350 + 0.052481391875 * 1.772454 / (2 * (113.152967261137 : ℝ))) * (1 + 0.001165342220) +
        8 / (12946 * 113.780490419052) + 0.122449887599 := by gcongr
    _ ≤ (0.159696228196 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481391875)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353248153) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281066061184) :
    parallelOracle 12946 0.011 xi bn cd ≤ 0.160667471870 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12946 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12946 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514481747 : ℝ) ≤ plow 12946 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.780490419052 : ℝ) ≤ √(12946 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281066061184 : ℝ) / (2 * 0.560514481747 * 113.780490419052)) * 0.159696228196 +
        0.281066061184 ^ 2 / (2 * 0.560514481747 * 113.780490419052) := by gcongr
    _ ≤ (0.160667471870 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481391875) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353248153)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281066061184) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12946 12946 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514481747 : ℝ) ≤ plow 12946 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.780490419052 : ℝ) ≤ √(12946 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12946 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12946 Θ 1.22 ≤ 0.011654902305 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.780490419052 := by gcongr <;> linarith
      _ ≤ (0.011654902305 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12946 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12946 12946 0.011 ≤ 0.008401149932 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12946 12946 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12946 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12946 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12946 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12946 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160667471870 + 0.011654902305 + (0.008401149932 : ℝ) *
        (1 + 2 * (0.281066061184 + 0.011654902305) / (0.560514481747 * 113.780490419052))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12946]

end BstLean.Part269.N12946

/-! The original eight local profiles supply actual 12946 moment certificates. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12946 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052481391875 ∧
    0 ≤ bN 12946 BstLean.Part154.csC (groupTheta g) ∧ bN 12946 BstLean.Part154.csC (groupTheta g) ≤ 0.001353248153 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12946 12946 0.011
      (momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12946 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12946 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12946 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229088174892 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12946 0.011
      (momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12946 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12946
/-! The actual computed-centre upper energy formula at 12946. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12946

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12946)
open BstLean.Part268 (cell12946)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084803124242
  | 2 => 0.085733907348
  | 3 => 0.086661192852
  | 4 => 0.087586014543
  | 5 => 0.088509634321
  | 6 => 0.089433577514
  | 7 => 0.090359671794
  | 8 => 0.091290089774
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12946 12946 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12946 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12946

/-! Actual upper energy certificates on all 43 source endpoints at 12946. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12946)
open BstLean.Part268 (cell12946)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12946 (gMinus 12946) (1 - (cell12946 i).lower) ≤ 1 ∧
    energyUpper 12946 (gMinus 12946) (BstLean.Part211.gPlus 12946)
      (finiteEnergy 12946 12946 0.011) (1 - (cell12946 i).lower) ≤
      (cell12946 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨10,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨11,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨12,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨13,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨14,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨15,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨16,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨17,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨18,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨19,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨20,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨21,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨22,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨23,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨24,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨25,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨26,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨27,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨28,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨29,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨30,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨31,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨32,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨33,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨34,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨35,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨36,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨37,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨38,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨39,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨40,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨41,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨42,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨43,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨44,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨45,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨46,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨47,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨48,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨49,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨50,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨51,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12946) (by norm_num)
        (q := 1 - (cell12946 ⟨52,by decide⟩).lower)
        (by norm_num [cell12946]) (by norm_num [cell12946])
      exact ⟨E.1,E.2.trans (by norm_num [cell12946])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12946

/-! Source-cell containment and simple scalar guards at 12946. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12946)
open BstLean.Part268 (cell12946)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12946 ⟨10,by decide⟩).lower ∧ (cell12946 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12946 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12946 ⟨11,by decide⟩).lower ∧ (cell12946 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12946 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12946 ⟨12,by decide⟩).lower ∧ (cell12946 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12946 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12946 ⟨13,by decide⟩).lower ∧ (cell12946 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12946 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12946 ⟨14,by decide⟩).lower ∧ (cell12946 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12946 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12946 ⟨15,by decide⟩).lower ∧ (cell12946 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12946 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12946 ⟨16,by decide⟩).lower ∧ (cell12946 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12946 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12946 ⟨17,by decide⟩).lower ∧ (cell12946 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12946 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12946 ⟨18,by decide⟩).lower ∧ (cell12946 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12946 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12946 ⟨19,by decide⟩).lower ∧ (cell12946 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12946 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12946 ⟨20,by decide⟩).lower ∧ (cell12946 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12946 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12946 ⟨21,by decide⟩).lower ∧ (cell12946 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12946 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12946 ⟨22,by decide⟩).lower ∧ (cell12946 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12946 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12946 ⟨23,by decide⟩).lower ∧ (cell12946 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12946 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12946 ⟨24,by decide⟩).lower ∧ (cell12946 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12946 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12946 ⟨25,by decide⟩).lower ∧ (cell12946 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12946 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12946 ⟨26,by decide⟩).lower ∧ (cell12946 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12946 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12946 ⟨27,by decide⟩).lower ∧ (cell12946 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12946 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12946 ⟨28,by decide⟩).lower ∧ (cell12946 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12946 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12946 ⟨29,by decide⟩).lower ∧ (cell12946 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12946 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12946 ⟨30,by decide⟩).lower ∧ (cell12946 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12946 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12946 ⟨31,by decide⟩).lower ∧ (cell12946 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12946 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12946 ⟨32,by decide⟩).lower ∧ (cell12946 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12946 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12946 ⟨33,by decide⟩).lower ∧ (cell12946 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12946 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12946 ⟨34,by decide⟩).lower ∧ (cell12946 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12946 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12946 ⟨35,by decide⟩).lower ∧ (cell12946 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12946 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12946 ⟨36,by decide⟩).lower ∧ (cell12946 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12946 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12946 ⟨37,by decide⟩).lower ∧ (cell12946 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12946 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12946 ⟨38,by decide⟩).lower ∧ (cell12946 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12946 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12946 ⟨39,by decide⟩).lower ∧ (cell12946 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12946 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12946 ⟨40,by decide⟩).lower ∧ (cell12946 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12946 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12946 ⟨41,by decide⟩).lower ∧ (cell12946 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12946 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12946 ⟨42,by decide⟩).lower ∧ (cell12946 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12946 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12946 ⟨43,by decide⟩).lower ∧ (cell12946 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12946 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12946 ⟨44,by decide⟩).lower ∧ (cell12946 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12946 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12946 ⟨45,by decide⟩).lower ∧ (cell12946 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12946 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12946 ⟨46,by decide⟩).lower ∧ (cell12946 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12946 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12946 ⟨47,by decide⟩).lower ∧ (cell12946 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12946 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12946 ⟨48,by decide⟩).lower ∧ (cell12946 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12946 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12946 ⟨49,by decide⟩).lower ∧ (cell12946 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12946 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12946 ⟨50,by decide⟩).lower ∧ (cell12946 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12946 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12946 ⟨51,by decide⟩).lower ∧ (cell12946 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12946 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12946 ⟨52,by decide⟩).lower ∧ (cell12946 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12946 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12946 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12946 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12946,cell12946,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12946 i).lower ∧
    (cell12946 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12946 i).upper ≤ (0.532 : ℝ) ∧
    (cell12946 i).centre ≤ (0.1 : ℝ) ∧ (cell12946 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12946 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12946 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12946

/-! The local source numeric instances at 12946 have no network premises. -/
namespace BstLean.Part269.N12946
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12946)
open BstLean.Part268 (cell12946)

noncomputable def sourceNumerics12946 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12946 (cell12946 i)
      scalarRow12946.M scalarRow12946.H scalarRow12946.xi := by
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
    energy_allowance := scalarRow12946.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12946]
    centre_nonneg := (scalarRow12946.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12946])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12946
/-! Actual 12947 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12947 ≤ (1.035463006028 : ℝ) := by
  have hr : (113.784884760674 : ℝ) ≤ √(12947 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.784884760674 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12947 12947 (11 / 1000) ≤
    (0.008400825479 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12947) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.784884760674 : ℝ) ≤ √(12947 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12947)
  have hdiv : K / √(12947 : ℝ) ≤ K / 113.784884760674 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.784884760674 ≤ (0.008400825479 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12947.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12947 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12947 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12947 := gPlus_lower 12947
end BstLean.Part269.N12947

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12947
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035463006027 : ℝ) ≤ wn 12947 := by
  have hn : √(12947 : ℝ) ≤ 113.784884760675 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12947 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.784884760675 ≤ 2 / √(12947 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246992958 : ℝ) ≤ rhoBar 12947 BstLean.Part154.csC ∧
    rhoBar 12947 BstLean.Part154.csC ≤ 0.000246993340 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035463006027 : ℝ) / (1.295212 * 12947) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035463006028 : ℝ) / (1.29521 * 12947) := by gcongr
      _ ≤ (0.000246993340 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12947 BstLean.Part154.csC) ≤ 0.000988034366 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12947 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) ≤ 0.000188655009 ∧
    cc1 (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) ≤ 0.000120042470 ∧
    cc2 (rhoBar 12947 BstLean.Part154.csC) ≤ 0.000069685616 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12947 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12947 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12947 BstLean.Part154.csC * nuR (rhoBar 12947 BstLean.Part154.csC)) ≤ 0.000494001932 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246993340 : ℝ) * 0.000988034366 := by gcongr
      _ ≤ (0.000494001932 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12947 BstLean.Part154.csC) * nuR (rhoBar 12947 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988034366 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12947 BstLean.Part154.csC) * rhoBar 12947 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246993340 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246993340 / 2 + 0.399 * 0.000988034366 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188655009 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494001932 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120042470 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246993340 / 1.414213562 := by gcongr
      _ ≤ (0.000069685616 : ℝ) := by norm_num

end BstLean.Part269.N12947

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12947
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) ≤ 1.53700E-7 := by
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12947 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12947 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12947 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188655009 : ℝ) ^ 2 + 0.000120042470 ^ 2 + 3 * 0.000069685616 ^ 2 +
        2 * 0.797885 * 0.000188655009 * 0.000120042470 + 2 * 0.000188655009 * 0.000069685616 +
        4 * 0.797885 * 0.000120042470 * 0.000069685616 := by gcongr
    _ ≤ (1.53700E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12947 BstLean.Part154.csC Θ ≤ 0.002577412172 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12947 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12947 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12947 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035463006028 * 1.53700E-7 / (0.000246992958 : ℝ) := by gcongr
    _ ≤ 0.002577412172 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12947 BstLean.Part154.csC Θ ≤ 0.002858809634 + 0.000651268444 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12947 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12947 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035463006028 : ℝ) * ((2 * Θ * 0.000246993340 +
        (6863 / 10000) * 0.000246993340 * 12947 * 0.000988034366) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002858809634 + 0.000651268444 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12947 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12947 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12947 0.011 Θ ∧ gammaRatio 12947 0.011 Θ ≤ 0.000084909923 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12947 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035463006028 : ℝ) * 0.525 / ((1 - 0.011) * 12947) := by gcongr
      _ ≤ (0.000084909923 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12947 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12947 0.011 Θ) :=
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
    badAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12947 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12947 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12947 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12947 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12947 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12947 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12947 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12947 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12947 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12947 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035463006028 : ℝ) * 12947 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279368190 + 0.003228680616 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12947

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12947
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12947 BstLean.Part154.csC) (piBar (rhoBar 12947 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12947 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12947 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12947 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12947 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12947 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12947 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12947 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12947 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12947 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12947 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051975857358 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12947) ≤ 0.010495573148 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12947 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035463006028)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010495573148 + 2 * 0.737676 / 12947) := by gcongr
    _ ≤ (0.051975857358 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12947 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12947

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12947
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514525264 : ℝ) ≤ plow 12947 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12947) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481025514)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353141391) : eMP 12947 0.011 xi bn ≤ 0.001165251167 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12947 : ℝ) * (1 - 0.011))) ≤ 0.000576187497 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353141391 / (12947 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576187497 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576187497 : ℝ) + 3.141593 * 0.052481025514 / (12947 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165251167 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481025514)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353141391) : PiBarMP 12947 12 0.011 xi bn ≤ 0.159690023611 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12947 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036785070219 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.157337367048 : ℝ) ≤ √((12947 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.784884760674 : ℝ) ≤ √(12947 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12947) ≤ 0.122445158618 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036785070219 + 0.052481025514 * 1.772454 / (2 * (113.157337367048 : ℝ))) * (1 + 0.001165251167) +
        8 / (12947 * 113.784884760674) + 0.122445158618 := by gcongr
    _ ≤ (0.159690023611 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481025514)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353141391) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281063232641) :
    parallelOracle 12947 0.011 xi bn cd ≤ 0.160661200023 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12947 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12947 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514525264 : ℝ) ≤ plow 12947 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.784884760674 : ℝ) ≤ √(12947 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281063232641 : ℝ) / (2 * 0.560514525264 * 113.784884760674)) * 0.159690023611 +
        0.281063232641 ^ 2 / (2 * 0.560514525264 * 113.784884760674) := by gcongr
    _ ≤ (0.160661200023 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052481025514) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353141391)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281063232641) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12947 12947 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514525264 : ℝ) ≤ plow 12947 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.784884760674 : ℝ) ≤ √(12947 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12947 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12947 Θ 1.22 ≤ 0.011654452196 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.784884760674 := by gcongr <;> linarith
      _ ≤ (0.011654452196 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12947 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12947 12947 0.011 ≤ 0.008400825479 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12947 12947 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12947 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12947 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12947 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12947 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160661200023 + 0.011654452196 + (0.008400825479 : ℝ) *
        (1 + 2 * (0.281063232641 + 0.011654452196) / (0.560514525264 * 113.784884760674))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12947]

end BstLean.Part269.N12947

/-! The original eight local profiles supply actual 12947 moment certificates. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12947 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052481025514 ∧
    0 ≤ bN 12947 BstLean.Part154.csC (groupTheta g) ∧ bN 12947 BstLean.Part154.csC (groupTheta g) ≤ 0.001353141391 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12947 12947 0.011
      (momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12947 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12947 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12947 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229087375283 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12947 0.011
      (momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12947 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12947
/-! The actual computed-centre upper energy formula at 12947. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12947

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12947)
open BstLean.Part268 (cell12947)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084800445046
  | 2 => 0.085731183966
  | 3 => 0.086658419679
  | 4 => 0.087583184626
  | 5 => 0.088506739119
  | 6 => 0.089430606617
  | 7 => 0.090356612608
  | 8 => 0.091286927174
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12947 12947 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12947 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12947

/-! Actual upper energy certificates on all 43 source endpoints at 12947. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12947)
open BstLean.Part268 (cell12947)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12947 (gMinus 12947) (1 - (cell12947 i).lower) ≤ 1 ∧
    energyUpper 12947 (gMinus 12947) (BstLean.Part211.gPlus 12947)
      (finiteEnergy 12947 12947 0.011) (1 - (cell12947 i).lower) ≤
      (cell12947 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨10,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨11,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨12,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨13,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨14,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨15,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨16,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨17,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨18,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨19,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨20,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨21,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨22,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨23,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨24,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨25,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨26,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨27,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨28,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨29,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨30,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨31,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨32,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨33,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨34,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨35,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨36,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨37,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨38,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨39,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨40,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨41,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨42,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨43,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨44,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨45,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨46,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨47,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨48,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨49,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨50,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨51,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12947) (by norm_num)
        (q := 1 - (cell12947 ⟨52,by decide⟩).lower)
        (by norm_num [cell12947]) (by norm_num [cell12947])
      exact ⟨E.1,E.2.trans (by norm_num [cell12947])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12947

/-! Source-cell containment and simple scalar guards at 12947. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12947)
open BstLean.Part268 (cell12947)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12947 ⟨10,by decide⟩).lower ∧ (cell12947 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12947 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12947 ⟨11,by decide⟩).lower ∧ (cell12947 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12947 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12947 ⟨12,by decide⟩).lower ∧ (cell12947 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12947 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12947 ⟨13,by decide⟩).lower ∧ (cell12947 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12947 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12947 ⟨14,by decide⟩).lower ∧ (cell12947 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12947 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12947 ⟨15,by decide⟩).lower ∧ (cell12947 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12947 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12947 ⟨16,by decide⟩).lower ∧ (cell12947 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12947 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12947 ⟨17,by decide⟩).lower ∧ (cell12947 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12947 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12947 ⟨18,by decide⟩).lower ∧ (cell12947 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12947 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12947 ⟨19,by decide⟩).lower ∧ (cell12947 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12947 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12947 ⟨20,by decide⟩).lower ∧ (cell12947 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12947 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12947 ⟨21,by decide⟩).lower ∧ (cell12947 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12947 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12947 ⟨22,by decide⟩).lower ∧ (cell12947 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12947 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12947 ⟨23,by decide⟩).lower ∧ (cell12947 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12947 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12947 ⟨24,by decide⟩).lower ∧ (cell12947 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12947 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12947 ⟨25,by decide⟩).lower ∧ (cell12947 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12947 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12947 ⟨26,by decide⟩).lower ∧ (cell12947 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12947 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12947 ⟨27,by decide⟩).lower ∧ (cell12947 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12947 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12947 ⟨28,by decide⟩).lower ∧ (cell12947 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12947 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12947 ⟨29,by decide⟩).lower ∧ (cell12947 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12947 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12947 ⟨30,by decide⟩).lower ∧ (cell12947 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12947 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12947 ⟨31,by decide⟩).lower ∧ (cell12947 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12947 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12947 ⟨32,by decide⟩).lower ∧ (cell12947 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12947 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12947 ⟨33,by decide⟩).lower ∧ (cell12947 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12947 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12947 ⟨34,by decide⟩).lower ∧ (cell12947 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12947 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12947 ⟨35,by decide⟩).lower ∧ (cell12947 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12947 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12947 ⟨36,by decide⟩).lower ∧ (cell12947 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12947 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12947 ⟨37,by decide⟩).lower ∧ (cell12947 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12947 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12947 ⟨38,by decide⟩).lower ∧ (cell12947 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12947 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12947 ⟨39,by decide⟩).lower ∧ (cell12947 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12947 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12947 ⟨40,by decide⟩).lower ∧ (cell12947 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12947 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12947 ⟨41,by decide⟩).lower ∧ (cell12947 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12947 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12947 ⟨42,by decide⟩).lower ∧ (cell12947 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12947 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12947 ⟨43,by decide⟩).lower ∧ (cell12947 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12947 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12947 ⟨44,by decide⟩).lower ∧ (cell12947 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12947 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12947 ⟨45,by decide⟩).lower ∧ (cell12947 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12947 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12947 ⟨46,by decide⟩).lower ∧ (cell12947 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12947 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12947 ⟨47,by decide⟩).lower ∧ (cell12947 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12947 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12947 ⟨48,by decide⟩).lower ∧ (cell12947 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12947 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12947 ⟨49,by decide⟩).lower ∧ (cell12947 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12947 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12947 ⟨50,by decide⟩).lower ∧ (cell12947 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12947 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12947 ⟨51,by decide⟩).lower ∧ (cell12947 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12947 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12947 ⟨52,by decide⟩).lower ∧ (cell12947 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12947 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12947 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12947 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12947,cell12947,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12947 i).lower ∧
    (cell12947 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12947 i).upper ≤ (0.532 : ℝ) ∧
    (cell12947 i).centre ≤ (0.1 : ℝ) ∧ (cell12947 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12947 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12947 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12947

/-! The local source numeric instances at 12947 have no network premises. -/
namespace BstLean.Part269.N12947
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12947)
open BstLean.Part268 (cell12947)

noncomputable def sourceNumerics12947 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12947 (cell12947 i)
      scalarRow12947.M scalarRow12947.H scalarRow12947.xi := by
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
    energy_allowance := scalarRow12947.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12947]
    centre_nonneg := (scalarRow12947.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12947])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12947
/-! Actual 12948 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12948 ≤ (1.035461624632 : ℝ) := by
  have hr : (113.789278932595 : ℝ) ≤ √(12948 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.789278932595 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12948 12948 (11 / 1000) ≤
    (0.008400501064 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12948) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.789278932595 : ℝ) ≤ √(12948 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12948)
  have hdiv : K / √(12948 : ℝ) ≤ K / 113.789278932595 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.789278932595 ≤ (0.008400501064 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12948.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12948 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12948 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12948 := gPlus_lower 12948
end BstLean.Part269.N12948

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12948
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035461624631 : ℝ) ≤ wn 12948 := by
  have hn : √(12948 : ℝ) ≤ 113.789278932596 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12948 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.789278932596 ≤ 2 / √(12948 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246973552 : ℝ) ≤ rhoBar 12948 BstLean.Part154.csC ∧
    rhoBar 12948 BstLean.Part154.csC ≤ 0.000246973935 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035461624631 : ℝ) / (1.295212 * 12948) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035461624632 : ℝ) / (1.29521 * 12948) := by gcongr
      _ ≤ (0.000246973935 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12948 BstLean.Part154.csC) ≤ 0.000987956737 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12948 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) ≤ 0.000188640187 ∧
    cc1 (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) ≤ 0.000120033039 ∧
    cc2 (rhoBar 12948 BstLean.Part154.csC) ≤ 0.000069680141 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12948 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12948 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12948 BstLean.Part154.csC * nuR (rhoBar 12948 BstLean.Part154.csC)) ≤ 0.000493963120 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246973935 : ℝ) * 0.000987956737 := by gcongr
      _ ≤ (0.000493963120 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12948 BstLean.Part154.csC) * nuR (rhoBar 12948 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987956737 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12948 BstLean.Part154.csC) * rhoBar 12948 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246973935 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246973935 / 2 + 0.399 * 0.000987956737 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188640187 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493963120 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120033039 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246973935 / 1.414213562 := by gcongr
      _ ≤ (0.000069680141 : ℝ) := by norm_num

end BstLean.Part269.N12948

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12948
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) ≤ 1.53675E-7 := by
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12948 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12948 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12948 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188640187 : ℝ) ^ 2 + 0.000120033039 ^ 2 + 3 * 0.000069680141 ^ 2 +
        2 * 0.797885 * 0.000188640187 * 0.000120033039 + 2 * 0.000188640187 * 0.000069680141 +
        4 * 0.797885 * 0.000120033039 * 0.000069680141 := by gcongr
    _ ≤ (1.53675E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12948 BstLean.Part154.csC Θ ≤ 0.002577191993 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12948 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12948 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12948 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035461624632 * 1.53675E-7 / (0.000246973552 : ℝ) := by gcongr
    _ ≤ 0.002577191993 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12948 BstLean.Part154.csC Θ ≤ 0.002858577396 + 0.000651216408 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12948 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12948 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035461624632 : ℝ) * ((2 * Θ * 0.000246973935 +
        (6863 / 10000) * 0.000246973935 * 12948 * 0.000987956737) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002858577396 + 0.000651216408 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12948 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12948 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12948 0.011 Θ ∧ gammaRatio 12948 0.011 Θ ≤ 0.000084903252 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12948 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035461624632 : ℝ) * 0.525 / ((1 - 0.011) * 12948) := by gcongr
      _ ≤ (0.000084903252 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12948 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12948 0.011 Θ) :=
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
    badAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12948 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12948 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12948 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12948 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12948 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12948 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12948 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12948 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12948 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12948 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035461624632 : ℝ) * 12948 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279135952 + 0.003228408401 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12948

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12948
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12948 BstLean.Part154.csC) (piBar (rhoBar 12948 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12948 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12948 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12948 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12948 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12948 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12948 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12948 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12948 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12948 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12948 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051973828662 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12948) ≤ 0.010495167843 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12948 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035461624632)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010495167843 + 2 * 0.737676 / 12948) := by gcongr
    _ ≤ (0.051973828662 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12948 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12948

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12948
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514568775 : ℝ) ≤ plow 12948 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12948) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480650363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353025797) : eMP 12948 0.011 xi bn ≤ 0.001165156359 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12948 : ℝ) * (1 - 0.011))) ≤ 0.000576140636 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001353025797 / (12948 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576140636 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576140636 : ℝ) + 3.141593 * 0.052480650363 / (12948 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165156359 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480650363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353025797) : PiBarMP 12948 12 0.011 xi bn ≤ 0.159683699118 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12948 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036783498978 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.161707304193 : ℝ) ≤ √((12948 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.789278932595 : ℝ) ≤ √(12948 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12948) ≤ 0.122440430184 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036783498978 + 0.052480650363 * 1.772454 / (2 * (113.161707304193 : ℝ))) * (1 + 0.001165156359) +
        8 / (12948 * 113.789278932595) + 0.122440430184 := by gcongr
    _ ≤ (0.159683699118 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480650363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353025797) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281060385149) :
    parallelOracle 12948 0.011 xi bn cd ≤ 0.160654807903 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12948 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12948 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514568775 : ℝ) ≤ plow 12948 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.789278932595 : ℝ) ≤ √(12948 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281060385149 : ℝ) / (2 * 0.560514568775 * 113.789278932595)) * 0.159683699118 +
        0.281060385149 ^ 2 / (2 * 0.560514568775 * 113.789278932595) := by gcongr
    _ ≤ (0.160654807903 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480650363) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001353025797)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281060385149) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12948 12948 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514568775 : ℝ) ≤ plow 12948 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.789278932595 : ℝ) ≤ √(12948 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12948 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12948 Θ 1.22 ≤ 0.011654002139 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.789278932595 := by gcongr <;> linarith
      _ ≤ (0.011654002139 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12948 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12948 12948 0.011 ≤ 0.008400501064 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12948 12948 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12948 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12948 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12948 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12948 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160654807903 + 0.011654002139 + (0.008400501064 : ℝ) *
        (1 + 2 * (0.281060385149 + 0.011654002139) / (0.560514568775 * 113.789278932595))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12948]

end BstLean.Part269.N12948

/-! The original eight local profiles supply actual 12948 moment certificates. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12948 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052480650363 ∧
    0 ≤ bN 12948 BstLean.Part154.csC (groupTheta g) ∧ bN 12948 BstLean.Part154.csC (groupTheta g) ≤ 0.001353025797 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12948 12948 0.011
      (momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12948 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12948 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12948 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229086556487 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12948 0.011
      (momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12948 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12948
/-! The actual computed-centre upper energy formula at 12948. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12948

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12948)
open BstLean.Part268 (cell12948)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084797766701
  | 2 => 0.085728461469
  | 3 => 0.086655647429
  | 4 => 0.087580355683
  | 5 => 0.088503844951
  | 6 => 0.089427636827
  | 7 => 0.090353554619
  | 8 => 0.091283765878
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12948 12948 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12948 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12948

/-! Actual upper energy certificates on all 43 source endpoints at 12948. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12948)
open BstLean.Part268 (cell12948)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12948 (gMinus 12948) (1 - (cell12948 i).lower) ≤ 1 ∧
    energyUpper 12948 (gMinus 12948) (BstLean.Part211.gPlus 12948)
      (finiteEnergy 12948 12948 0.011) (1 - (cell12948 i).lower) ≤
      (cell12948 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨10,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨11,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨12,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨13,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨14,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨15,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨16,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨17,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨18,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨19,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨20,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨21,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨22,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨23,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨24,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨25,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨26,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨27,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨28,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨29,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨30,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨31,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨32,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨33,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨34,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨35,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨36,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨37,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨38,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨39,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨40,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨41,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨42,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨43,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨44,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨45,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨46,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨47,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨48,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨49,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨50,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨51,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12948) (by norm_num)
        (q := 1 - (cell12948 ⟨52,by decide⟩).lower)
        (by norm_num [cell12948]) (by norm_num [cell12948])
      exact ⟨E.1,E.2.trans (by norm_num [cell12948])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12948

/-! Source-cell containment and simple scalar guards at 12948. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12948)
open BstLean.Part268 (cell12948)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12948 ⟨10,by decide⟩).lower ∧ (cell12948 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12948 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12948 ⟨11,by decide⟩).lower ∧ (cell12948 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12948 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12948 ⟨12,by decide⟩).lower ∧ (cell12948 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12948 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12948 ⟨13,by decide⟩).lower ∧ (cell12948 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12948 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12948 ⟨14,by decide⟩).lower ∧ (cell12948 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12948 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12948 ⟨15,by decide⟩).lower ∧ (cell12948 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12948 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12948 ⟨16,by decide⟩).lower ∧ (cell12948 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12948 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12948 ⟨17,by decide⟩).lower ∧ (cell12948 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12948 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12948 ⟨18,by decide⟩).lower ∧ (cell12948 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12948 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12948 ⟨19,by decide⟩).lower ∧ (cell12948 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12948 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12948 ⟨20,by decide⟩).lower ∧ (cell12948 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12948 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12948 ⟨21,by decide⟩).lower ∧ (cell12948 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12948 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12948 ⟨22,by decide⟩).lower ∧ (cell12948 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12948 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12948 ⟨23,by decide⟩).lower ∧ (cell12948 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12948 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12948 ⟨24,by decide⟩).lower ∧ (cell12948 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12948 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12948 ⟨25,by decide⟩).lower ∧ (cell12948 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12948 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12948 ⟨26,by decide⟩).lower ∧ (cell12948 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12948 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12948 ⟨27,by decide⟩).lower ∧ (cell12948 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12948 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12948 ⟨28,by decide⟩).lower ∧ (cell12948 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12948 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12948 ⟨29,by decide⟩).lower ∧ (cell12948 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12948 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12948 ⟨30,by decide⟩).lower ∧ (cell12948 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12948 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12948 ⟨31,by decide⟩).lower ∧ (cell12948 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12948 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12948 ⟨32,by decide⟩).lower ∧ (cell12948 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12948 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12948 ⟨33,by decide⟩).lower ∧ (cell12948 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12948 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12948 ⟨34,by decide⟩).lower ∧ (cell12948 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12948 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12948 ⟨35,by decide⟩).lower ∧ (cell12948 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12948 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12948 ⟨36,by decide⟩).lower ∧ (cell12948 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12948 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12948 ⟨37,by decide⟩).lower ∧ (cell12948 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12948 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12948 ⟨38,by decide⟩).lower ∧ (cell12948 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12948 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12948 ⟨39,by decide⟩).lower ∧ (cell12948 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12948 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12948 ⟨40,by decide⟩).lower ∧ (cell12948 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12948 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12948 ⟨41,by decide⟩).lower ∧ (cell12948 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12948 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12948 ⟨42,by decide⟩).lower ∧ (cell12948 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12948 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12948 ⟨43,by decide⟩).lower ∧ (cell12948 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12948 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12948 ⟨44,by decide⟩).lower ∧ (cell12948 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12948 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12948 ⟨45,by decide⟩).lower ∧ (cell12948 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12948 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12948 ⟨46,by decide⟩).lower ∧ (cell12948 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12948 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12948 ⟨47,by decide⟩).lower ∧ (cell12948 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12948 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12948 ⟨48,by decide⟩).lower ∧ (cell12948 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12948 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12948 ⟨49,by decide⟩).lower ∧ (cell12948 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12948 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12948 ⟨50,by decide⟩).lower ∧ (cell12948 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12948 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12948 ⟨51,by decide⟩).lower ∧ (cell12948 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12948 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12948 ⟨52,by decide⟩).lower ∧ (cell12948 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12948 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12948 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12948 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12948,cell12948,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12948 i).lower ∧
    (cell12948 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12948 i).upper ≤ (0.532 : ℝ) ∧
    (cell12948 i).centre ≤ (0.1 : ℝ) ∧ (cell12948 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12948 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12948 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12948

/-! The local source numeric instances at 12948 have no network premises. -/
namespace BstLean.Part269.N12948
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12948)
open BstLean.Part268 (cell12948)

noncomputable def sourceNumerics12948 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12948 (cell12948 i)
      scalarRow12948.M scalarRow12948.H scalarRow12948.xi := by
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
    energy_allowance := scalarRow12948.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12948]
    centre_nonneg := (scalarRow12948.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12948])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12948
/-! Actual 12949 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12949 ≤ (1.035460243397 : ℝ) := by
  have hr : (113.793672934834 : ℝ) ≤ √(12949 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.793672934834 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12949 12949 (11 / 1000) ≤
    (0.008400176686 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12949) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.793672934834 : ℝ) ≤ √(12949 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12949)
  have hdiv : K / √(12949 : ℝ) ≤ K / 113.793672934834 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.793672934834 ≤ (0.008400176686 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12949.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12949 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12949 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12949 := gPlus_lower 12949
end BstLean.Part269.N12949

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12949
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035460243396 : ℝ) ≤ wn 12949 := by
  have hn : √(12949 : ℝ) ≤ 113.793672934835 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12949 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.793672934835 ≤ 2 / √(12949 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246954150 : ℝ) ≤ rhoBar 12949 BstLean.Part154.csC ∧
    rhoBar 12949 BstLean.Part154.csC ≤ 0.000246954532 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035460243396 : ℝ) / (1.295212 * 12949) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035460243397 : ℝ) / (1.29521 * 12949) := by gcongr
      _ ≤ (0.000246954532 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12949 BstLean.Part154.csC) ≤ 0.000987879115 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12949 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) ≤ 0.000188625366 ∧
    cc1 (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) ≤ 0.000120023608 ∧
    cc2 (rhoBar 12949 BstLean.Part154.csC) ≤ 0.000069674667 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12949 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12949 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12949 BstLean.Part154.csC * nuR (rhoBar 12949 BstLean.Part154.csC)) ≤ 0.000493924311 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246954532 : ℝ) * 0.000987879115 := by gcongr
      _ ≤ (0.000493924311 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12949 BstLean.Part154.csC) * nuR (rhoBar 12949 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987879115 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12949 BstLean.Part154.csC) * rhoBar 12949 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246954532 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246954532 / 2 + 0.399 * 0.000987879115 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188625366 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493924311 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120023608 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246954532 / 1.414213562 := by gcongr
      _ ≤ (0.000069674667 : ℝ) := by norm_num

end BstLean.Part269.N12949

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12949
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) ≤ 1.53651E-7 := by
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12949 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12949 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12949 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188625366 : ℝ) ^ 2 + 0.000120023608 ^ 2 + 3 * 0.000069674667 ^ 2 +
        2 * 0.797885 * 0.000188625366 * 0.000120023608 + 2 * 0.000188625366 * 0.000069674667 +
        4 * 0.797885 * 0.000120023608 * 0.000069674667 := by gcongr
    _ ≤ (1.53651E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12949 BstLean.Part154.csC Θ ≤ 0.002576988512 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12949 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12949 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12949 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035460243397 * 1.53651E-7 / (0.000246954150 : ℝ) := by gcongr
    _ ≤ 0.002576988512 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12949 BstLean.Part154.csC Θ ≤ 0.002858345168 + 0.000651164378 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12949 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12949 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035460243397 : ℝ) * ((2 * Θ * 0.000246954532 +
        (6863 / 10000) * 0.000246954532 * 12949 * 0.000987879115) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002858345168 + 0.000651164378 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12949 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12949 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12949 0.011 Θ ∧ gammaRatio 12949 0.011 Θ ≤ 0.000084896582 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12949 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035460243397 : ℝ) * 0.525 / ((1 - 0.011) * 12949) := by gcongr
      _ ≤ (0.000084896582 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12949 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12949 0.011 Θ) :=
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
    badAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12949 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12949 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12949 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12949 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12949 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12949 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12949 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12949 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12949 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12949 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035460243397 : ℝ) * 12949 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003278903724 + 0.003228152890 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12949

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12949
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12949 BstLean.Part154.csC) (piBar (rhoBar 12949 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12949 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12949 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12949 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12949 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12949 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12949 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12949 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12949 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12949 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12949 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051971800203 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12949) ≤ 0.010494762585 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12949 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035460243397)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010494762585 + 2 * 0.737676 / 12949) := by gcongr
    _ ≤ (0.051971800203 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12949 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12949

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12949
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514612278 : ℝ) ≤ plow 12949 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12949) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480283992)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352918969) : eMP 12949 0.011 xi bn ≤ 0.001165065293 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12949 : ℝ) * (1 - 0.011))) ≤ 0.000576095645 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352918969 / (12949 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576095645 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576095645 : ℝ) + 3.141593 * 0.052480283992 / (12949 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001165065293 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480283992)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352918969) : PiBarMP 12949 12 0.011 xi bn ≤ 0.159677494614 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12949 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036782046830 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.166077072592 : ℝ) ≤ √((12949 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.793672934834 : ℝ) ≤ √(12949 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12949) ≤ 0.122435702298 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036782046830 + 0.052480283992 * 1.772454 / (2 * (113.166077072592 : ℝ))) * (1 + 0.001165065293) +
        8 / (12949 * 113.793672934834) + 0.122435702298 := by gcongr
    _ ≤ (0.159677494614 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480283992)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352918969) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281057557055) :
    parallelOracle 12949 0.011 xi bn cd ≤ 0.160648536153 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12949 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12949 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514612278 : ℝ) ≤ plow 12949 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.793672934834 : ℝ) ≤ √(12949 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281057557055 : ℝ) / (2 * 0.560514612278 * 113.793672934834)) * 0.159677494614 +
        0.281057557055 ^ 2 / (2 * 0.560514612278 * 113.793672934834) := by gcongr
    _ ≤ (0.160648536153 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480283992) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352918969)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281057557055) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12949 12949 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514612278 : ℝ) ≤ plow 12949 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.793672934834 : ℝ) ≤ √(12949 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12949 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12949 Θ 1.22 ≤ 0.011653552134 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.793672934834 := by gcongr <;> linarith
      _ ≤ (0.011653552134 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12949 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12949 12949 0.011 ≤ 0.008400176686 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12949 12949 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12949 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12949 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12949 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12949 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160648536153 + 0.011653552134 + (0.008400176686 : ℝ) *
        (1 + 2 * (0.281057557055 + 0.011653552134) / (0.560514612278 * 113.793672934834))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12949]

end BstLean.Part269.N12949

/-! The original eight local profiles supply actual 12949 moment certificates. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12949 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052480283992 ∧
    0 ≤ bN 12949 BstLean.Part154.csC (groupTheta g) ∧ bN 12949 BstLean.Part154.csC (groupTheta g) ≤ 0.001352918969 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12949 12949 0.011
      (momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12949 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12949 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12949 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229085756852 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12949 0.011
      (momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12949 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12949
/-! The actual computed-centre upper energy formula at 12949. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12949

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12949)
open BstLean.Part268 (cell12949)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084795089207
  | 2 => 0.085725739855
  | 3 => 0.086652876103
  | 4 => 0.087577527712
  | 5 => 0.088500951816
  | 6 => 0.089424668143
  | 7 => 0.090350497824
  | 8 => 0.091280605885
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12949 12949 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12949 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12949

/-! Actual upper energy certificates on all 43 source endpoints at 12949. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12949)
open BstLean.Part268 (cell12949)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12949 (gMinus 12949) (1 - (cell12949 i).lower) ≤ 1 ∧
    energyUpper 12949 (gMinus 12949) (BstLean.Part211.gPlus 12949)
      (finiteEnergy 12949 12949 0.011) (1 - (cell12949 i).lower) ≤
      (cell12949 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨10,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨11,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨12,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨13,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨14,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨15,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨16,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨17,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨18,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨19,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨20,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨21,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨22,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨23,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨24,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨25,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨26,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨27,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨28,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨29,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨30,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨31,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨32,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨33,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨34,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨35,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨36,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨37,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨38,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨39,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨40,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨41,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨42,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨43,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨44,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨45,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨46,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨47,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨48,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨49,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨50,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨51,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12949) (by norm_num)
        (q := 1 - (cell12949 ⟨52,by decide⟩).lower)
        (by norm_num [cell12949]) (by norm_num [cell12949])
      exact ⟨E.1,E.2.trans (by norm_num [cell12949])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12949

/-! Source-cell containment and simple scalar guards at 12949. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12949)
open BstLean.Part268 (cell12949)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12949 ⟨10,by decide⟩).lower ∧ (cell12949 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12949 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12949 ⟨11,by decide⟩).lower ∧ (cell12949 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12949 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12949 ⟨12,by decide⟩).lower ∧ (cell12949 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12949 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12949 ⟨13,by decide⟩).lower ∧ (cell12949 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12949 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12949 ⟨14,by decide⟩).lower ∧ (cell12949 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12949 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12949 ⟨15,by decide⟩).lower ∧ (cell12949 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12949 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12949 ⟨16,by decide⟩).lower ∧ (cell12949 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12949 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12949 ⟨17,by decide⟩).lower ∧ (cell12949 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12949 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12949 ⟨18,by decide⟩).lower ∧ (cell12949 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12949 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12949 ⟨19,by decide⟩).lower ∧ (cell12949 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12949 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12949 ⟨20,by decide⟩).lower ∧ (cell12949 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12949 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12949 ⟨21,by decide⟩).lower ∧ (cell12949 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12949 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12949 ⟨22,by decide⟩).lower ∧ (cell12949 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12949 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12949 ⟨23,by decide⟩).lower ∧ (cell12949 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12949 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12949 ⟨24,by decide⟩).lower ∧ (cell12949 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12949 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12949 ⟨25,by decide⟩).lower ∧ (cell12949 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12949 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12949 ⟨26,by decide⟩).lower ∧ (cell12949 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12949 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12949 ⟨27,by decide⟩).lower ∧ (cell12949 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12949 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12949 ⟨28,by decide⟩).lower ∧ (cell12949 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12949 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12949 ⟨29,by decide⟩).lower ∧ (cell12949 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12949 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12949 ⟨30,by decide⟩).lower ∧ (cell12949 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12949 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12949 ⟨31,by decide⟩).lower ∧ (cell12949 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12949 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12949 ⟨32,by decide⟩).lower ∧ (cell12949 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12949 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12949 ⟨33,by decide⟩).lower ∧ (cell12949 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12949 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12949 ⟨34,by decide⟩).lower ∧ (cell12949 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12949 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12949 ⟨35,by decide⟩).lower ∧ (cell12949 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12949 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12949 ⟨36,by decide⟩).lower ∧ (cell12949 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12949 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12949 ⟨37,by decide⟩).lower ∧ (cell12949 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12949 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12949 ⟨38,by decide⟩).lower ∧ (cell12949 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12949 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12949 ⟨39,by decide⟩).lower ∧ (cell12949 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12949 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12949 ⟨40,by decide⟩).lower ∧ (cell12949 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12949 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12949 ⟨41,by decide⟩).lower ∧ (cell12949 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12949 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12949 ⟨42,by decide⟩).lower ∧ (cell12949 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12949 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12949 ⟨43,by decide⟩).lower ∧ (cell12949 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12949 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12949 ⟨44,by decide⟩).lower ∧ (cell12949 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12949 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12949 ⟨45,by decide⟩).lower ∧ (cell12949 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12949 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12949 ⟨46,by decide⟩).lower ∧ (cell12949 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12949 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12949 ⟨47,by decide⟩).lower ∧ (cell12949 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12949 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12949 ⟨48,by decide⟩).lower ∧ (cell12949 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12949 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12949 ⟨49,by decide⟩).lower ∧ (cell12949 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12949 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12949 ⟨50,by decide⟩).lower ∧ (cell12949 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12949 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12949 ⟨51,by decide⟩).lower ∧ (cell12949 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12949 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12949 ⟨52,by decide⟩).lower ∧ (cell12949 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12949 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12949 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12949 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12949,cell12949,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12949 i).lower ∧
    (cell12949 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12949 i).upper ≤ (0.532 : ℝ) ∧
    (cell12949 i).centre ≤ (0.1 : ℝ) ∧ (cell12949 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12949 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12949 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12949

/-! The local source numeric instances at 12949 have no network premises. -/
namespace BstLean.Part269.N12949
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12949)
open BstLean.Part268 (cell12949)

noncomputable def sourceNumerics12949 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12949 (cell12949 i)
      scalarRow12949.M scalarRow12949.H scalarRow12949.xi := by
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
    energy_allowance := scalarRow12949.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12949]
    centre_nonneg := (scalarRow12949.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12949])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12949