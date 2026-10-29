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
import BstLean.Part269Direction15
import BstLean.Part269Shared15
import BstLean.Part269Finite
import BstLean.Part269Rows15
import BstLean.Part269Source
/-! Actual 12725 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12725 ≤ (1.035773718421 : ℝ) := by
  have hr : (112.805141726784 : ℝ) ≤ √(12725 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.805141726784 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12725 12725 (11 / 1000) ≤
    (0.008473789468 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12725) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.805141726784 : ℝ) ≤ √(12725 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12725)
  have hdiv : K / √(12725 : ℝ) ≤ K / 112.805141726784 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.805141726784 ≤ (0.008473789468 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12725.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12725 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12725 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12725 := gPlus_lower 12725
end BstLean.Part269.N12725

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12725
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035773718420 : ℝ) ≤ wn 12725 := by
  have hn : √(12725 : ℝ) ≤ 112.805141726785 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12725 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.805141726785 ≤ 2 / √(12725 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251377398 : ℝ) ≤ rhoBar 12725 BstLean.Part154.csC ∧
    rhoBar 12725 BstLean.Part154.csC ≤ 0.000251377787 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035773718420 : ℝ) / (1.295212 * 12725) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035773718421 : ℝ) / (1.29521 * 12725) := by gcongr
      _ ≤ (0.000251377787 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12725 BstLean.Part154.csC) ≤ 0.001005574339 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12725 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) ≤ 0.000192004032 ∧
    cc1 (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) ≤ 0.000122173444 ∧
    cc2 (rhoBar 12725 BstLean.Part154.csC) ≤ 0.000070922625 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12725 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12725 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12725 BstLean.Part154.csC * nuR (rhoBar 12725 BstLean.Part154.csC)) ≤ 0.000502771372 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251377787 : ℝ) * 0.001005574339 := by gcongr
      _ ≤ (0.000502771372 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12725 BstLean.Part154.csC) * nuR (rhoBar 12725 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005574339 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12725 BstLean.Part154.csC) * rhoBar 12725 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251377787 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251377787 / 2 + 0.399 * 0.001005574339 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192004032 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502771372 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122173444 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251377787 / 1.414213562 := by gcongr
      _ ≤ (0.000070922625 : ℝ) := by norm_num

end BstLean.Part269.N12725

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12725
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) ≤ 1.59205E-7 := by
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12725 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12725 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12725 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192004032 : ℝ) ^ 2 + 0.000122173444 ^ 2 + 3 * 0.000070922625 ^ 2 +
        2 * 0.797885 * 0.000192004032 * 0.000122173444 + 2 * 0.000192004032 * 0.000070922625 +
        4 * 0.797885 * 0.000122173444 * 0.000070922625 := by gcongr
    _ ≤ (1.59205E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12725 BstLean.Part154.csC Θ ≤ 0.002623948791 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12725 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12725 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12725 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035773718421 * 1.59205E-7 / (0.000251377398 : ℝ) := by gcongr
    _ ≤ 0.002623948791 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12725 BstLean.Part154.csC Θ ≤ 0.002911306747 + 0.000663028185 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12725 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12725 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035773718421 : ℝ) * ((2 * Θ * 0.000251377787 +
        (6863 / 10000) * 0.000251377787 * 12725 * 0.001005574339) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002911306747 + 0.000663028185 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12725 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12725 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12725 0.011 Θ ∧ gammaRatio 12725 0.011 Θ ≤ 0.000086417183 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12725 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035773718421 : ℝ) * 0.525 / ((1 - 0.011) * 12725) := by gcongr
      _ ≤ (0.000086417183 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12725 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12725 0.011 Θ) :=
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
    badAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12725 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12725 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12725 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12725 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12725 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12725 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12725 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12725 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12725 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12725 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035773718421 : ℝ) * 12725 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003470390978 + 0.003286976976 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12725

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12725
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12725 BstLean.Part154.csC) (piBar (rhoBar 12725 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12725 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12725 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12725 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12725 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12725 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12725 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12725 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12725 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12725 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12725 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052432172377 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12725) ≤ 0.010586730027 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12725 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035773718421)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010586730027 + 2 * 0.737676 / 12725) := by gcongr
    _ ≤ (0.052432172377 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12725 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12725

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12725
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504696644 : ℝ) ≤ plow 12725 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12725) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702653891)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377573116) : eMP 12725 0.011 xi bn ≤ 0.001185986616 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12725 : ℝ) * (1 - 0.011))) ≤ 0.000586415240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377573116 / (12725 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586415240 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586415240 : ℝ) + 3.141593 * 0.052702653891 / (12725 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185986616 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702653891)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377573116) : PiBarMP 12725 12 0.011 xi bn ≤ 0.161090727741 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12725 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037115672108 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.182997820525 : ℝ) ≤ √((12725 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.805141726784 : ℝ) ≤ √(12725 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12725) ≤ 0.123508627794 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037115672108 + 0.052702653891 * 1.772454 / (2 * (112.182997820525 : ℝ))) * (1 + 0.001185986616) +
        8 / (12725 * 112.805141726784) + 0.123508627794 := by gcongr
    _ ≤ (0.161090727741 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702653891)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377573116) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282002758235) :
    parallelOracle 12725 0.011 xi bn cd ≤ 0.162078849754 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12725 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12725 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504696644 : ℝ) ≤ plow 12725 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.805141726784 : ℝ) ≤ √(12725 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282002758235 : ℝ) / (2 * 0.560504696644 * 112.805141726784)) * 0.161090727741 +
        0.282002758235 ^ 2 / (2 * 0.560504696644 * 112.805141726784) := by gcongr
    _ ≤ (0.162078849754 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702653891) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377573116)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282002758235) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12725 12725 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504696644 : ℝ) ≤ plow 12725 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.805141726784 : ℝ) ≤ √(12725 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12725 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12725 Θ 1.22 ≤ 0.011755674252 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.805141726784 := by gcongr <;> linarith
      _ ≤ (0.011755674252 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12725 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12725 12725 0.011 ≤ 0.008473789468 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12725 12725 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12725 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12725 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12725 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12725 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162078849754 + 0.011755674252 + (0.008473789468 : ℝ) *
        (1 + 2 * (0.282002758235 + 0.011755674252) / (0.560504696644 * 112.805141726784))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12725]

end BstLean.Part269.N12725

/-! The original eight local profiles supply actual 12725 moment certificates. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12725 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052702653891 ∧
    0 ≤ bN 12725 BstLean.Part154.csC (groupTheta g) ∧ bN 12725 BstLean.Part154.csC (groupTheta g) ≤ 0.001377573116 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12725 12725 0.011
      (momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12725 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12725 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12725 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229570585858 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12725 0.011
      (momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12725 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12725
/-! The actual computed-centre upper energy formula at 12725. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12725

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12725)
open BstLean.Part268 (cell12725)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085417684743
  | 2 => 0.086359108298
  | 3 => 0.087298479310
  | 4 => 0.088237171483
  | 5 => 0.089176847838
  | 6 => 0.090119503872
  | 7 => 0.091067514813
  | 8 => 0.092023687023
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12725 12725 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12725 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12725

/-! Actual upper energy certificates on all 43 source endpoints at 12725. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12725)
open BstLean.Part268 (cell12725)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12725 (gMinus 12725) (1 - (cell12725 i).lower) ≤ 1 ∧
    energyUpper 12725 (gMinus 12725) (BstLean.Part211.gPlus 12725)
      (finiteEnergy 12725 12725 0.011) (1 - (cell12725 i).lower) ≤
      (cell12725 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨10,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨11,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨12,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨13,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨14,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨15,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨16,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨17,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨18,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨19,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨20,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨21,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨22,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨23,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨24,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨25,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨26,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨27,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨28,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨29,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨30,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨31,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨32,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨33,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨34,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨35,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨36,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨37,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨38,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨39,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨40,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨41,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨42,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨43,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨44,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨45,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨46,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨47,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨48,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨49,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨50,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨51,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12725) (by norm_num)
        (q := 1 - (cell12725 ⟨52,by decide⟩).lower)
        (by norm_num [cell12725]) (by norm_num [cell12725])
      exact ⟨E.1,E.2.trans (by norm_num [cell12725])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12725

/-! Source-cell containment and simple scalar guards at 12725. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12725)
open BstLean.Part268 (cell12725)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12725 ⟨10,by decide⟩).lower ∧ (cell12725 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12725 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12725 ⟨11,by decide⟩).lower ∧ (cell12725 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12725 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12725 ⟨12,by decide⟩).lower ∧ (cell12725 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12725 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12725 ⟨13,by decide⟩).lower ∧ (cell12725 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12725 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12725 ⟨14,by decide⟩).lower ∧ (cell12725 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12725 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12725 ⟨15,by decide⟩).lower ∧ (cell12725 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12725 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12725 ⟨16,by decide⟩).lower ∧ (cell12725 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12725 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12725 ⟨17,by decide⟩).lower ∧ (cell12725 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12725 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12725 ⟨18,by decide⟩).lower ∧ (cell12725 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12725 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12725 ⟨19,by decide⟩).lower ∧ (cell12725 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12725 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12725 ⟨20,by decide⟩).lower ∧ (cell12725 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12725 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12725 ⟨21,by decide⟩).lower ∧ (cell12725 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12725 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12725 ⟨22,by decide⟩).lower ∧ (cell12725 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12725 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12725 ⟨23,by decide⟩).lower ∧ (cell12725 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12725 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12725 ⟨24,by decide⟩).lower ∧ (cell12725 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12725 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12725 ⟨25,by decide⟩).lower ∧ (cell12725 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12725 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12725 ⟨26,by decide⟩).lower ∧ (cell12725 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12725 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12725 ⟨27,by decide⟩).lower ∧ (cell12725 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12725 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12725 ⟨28,by decide⟩).lower ∧ (cell12725 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12725 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12725 ⟨29,by decide⟩).lower ∧ (cell12725 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12725 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12725 ⟨30,by decide⟩).lower ∧ (cell12725 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12725 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12725 ⟨31,by decide⟩).lower ∧ (cell12725 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12725 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12725 ⟨32,by decide⟩).lower ∧ (cell12725 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12725 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12725 ⟨33,by decide⟩).lower ∧ (cell12725 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12725 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12725 ⟨34,by decide⟩).lower ∧ (cell12725 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12725 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12725 ⟨35,by decide⟩).lower ∧ (cell12725 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12725 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12725 ⟨36,by decide⟩).lower ∧ (cell12725 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12725 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12725 ⟨37,by decide⟩).lower ∧ (cell12725 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12725 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12725 ⟨38,by decide⟩).lower ∧ (cell12725 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12725 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12725 ⟨39,by decide⟩).lower ∧ (cell12725 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12725 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12725 ⟨40,by decide⟩).lower ∧ (cell12725 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12725 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12725 ⟨41,by decide⟩).lower ∧ (cell12725 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12725 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12725 ⟨42,by decide⟩).lower ∧ (cell12725 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12725 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12725 ⟨43,by decide⟩).lower ∧ (cell12725 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12725 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12725 ⟨44,by decide⟩).lower ∧ (cell12725 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12725 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12725 ⟨45,by decide⟩).lower ∧ (cell12725 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12725 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12725 ⟨46,by decide⟩).lower ∧ (cell12725 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12725 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12725 ⟨47,by decide⟩).lower ∧ (cell12725 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12725 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12725 ⟨48,by decide⟩).lower ∧ (cell12725 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12725 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12725 ⟨49,by decide⟩).lower ∧ (cell12725 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12725 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12725 ⟨50,by decide⟩).lower ∧ (cell12725 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12725 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12725 ⟨51,by decide⟩).lower ∧ (cell12725 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12725 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12725 ⟨52,by decide⟩).lower ∧ (cell12725 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12725 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12725 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12725 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12725,cell12725,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12725 i).lower ∧
    (cell12725 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12725 i).upper ≤ (0.532 : ℝ) ∧
    (cell12725 i).centre ≤ (0.1 : ℝ) ∧ (cell12725 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12725 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12725 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12725

/-! The local source numeric instances at 12725 have no network premises. -/
namespace BstLean.Part269.N12725
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12725)
open BstLean.Part268 (cell12725)

noncomputable def sourceNumerics12725 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12725 (cell12725 i)
      scalarRow12725.M scalarRow12725.H scalarRow12725.xi := by
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
    energy_allowance := scalarRow12725.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12725]
    centre_nonneg := (scalarRow12725.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12725])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12725
/-! Actual 12726 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12726 ≤ (1.035772300507 : ℝ) := by
  have hr : (112.809574061778 : ℝ) ≤ √(12726 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.809574061778 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12726 12726 (11 / 1000) ≤
    (0.008473456527 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12726) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.809574061778 : ℝ) ≤ √(12726 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12726)
  have hdiv : K / √(12726 : ℝ) ≤ K / 112.809574061778 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.809574061778 ≤ (0.008473456527 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12726.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12726 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12726 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12726 := gPlus_lower 12726
end BstLean.Part269.N12726

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12726
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035772300506 : ℝ) ≤ wn 12726 := by
  have hn : √(12726 : ℝ) ≤ 112.809574061779 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12726 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.809574061779 ≤ 2 / √(12726 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251357301 : ℝ) ≤ rhoBar 12726 BstLean.Part154.csC ∧
    rhoBar 12726 BstLean.Part154.csC ≤ 0.000251357690 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035772300506 : ℝ) / (1.295212 * 12726) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035772300507 : ℝ) / (1.29521 * 12726) := by gcongr
      _ ≤ (0.000251357690 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12726 BstLean.Part154.csC) ≤ 0.001005493941 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12726 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) ≤ 0.000191988681 ∧
    cc1 (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) ≤ 0.000122163676 ∧
    cc2 (rhoBar 12726 BstLean.Part154.csC) ≤ 0.000070916955 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12726 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12726 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12726 BstLean.Part154.csC * nuR (rhoBar 12726 BstLean.Part154.csC)) ≤ 0.000502731176 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251357690 : ℝ) * 0.001005493941 := by gcongr
      _ ≤ (0.000502731176 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12726 BstLean.Part154.csC) * nuR (rhoBar 12726 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005493941 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12726 BstLean.Part154.csC) * rhoBar 12726 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251357690 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251357690 / 2 + 0.399 * 0.001005493941 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191988681 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502731176 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122163676 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251357690 / 1.414213562 := by gcongr
      _ ≤ (0.000070916955 : ℝ) := by norm_num

end BstLean.Part269.N12726

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12726
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) ≤ 1.59179E-7 := by
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12726 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12726 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12726 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191988681 : ℝ) ^ 2 + 0.000122163676 ^ 2 + 3 * 0.000070916955 ^ 2 +
        2 * 0.797885 * 0.000191988681 * 0.000122163676 + 2 * 0.000191988681 * 0.000070916955 +
        4 * 0.797885 * 0.000122163676 * 0.000070916955 := by gcongr
    _ ≤ (1.59179E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12726 BstLean.Part154.csC Θ ≤ 0.002623726439 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12726 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12726 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12726 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035772300507 * 1.59179E-7 / (0.000251357301 : ℝ) := by gcongr
    _ ≤ 0.002623726439 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12726 BstLean.Part154.csC Θ ≤ 0.002911066013 + 0.000662974270 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12726 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12726 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035772300507 : ℝ) * ((2 * Θ * 0.000251357690 +
        (6863 / 10000) * 0.000251357690 * 12726 * 0.001005493941) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002911066013 + 0.000662974270 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12726 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12726 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12726 0.011 Θ ∧ gammaRatio 12726 0.011 Θ ≤ 0.000086410274 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12726 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035772300507 : ℝ) * 0.525 / ((1 - 0.011) * 12726) := by gcongr
      _ ≤ (0.000086410274 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12726 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12726 0.011 Θ) :=
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
    badAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12726 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12726 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12726 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12726 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12726 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12726 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12726 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12726 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12726 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12726 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035772300507 : ℝ) * 12726 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003470150244 + 0.003286700709 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12726

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12726
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12726 BstLean.Part154.csC) (piBar (rhoBar 12726 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12726 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12726 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12726 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12726 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12726 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12726 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12726 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12726 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12726 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12726 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052430089979 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12726) ≤ 0.010586314070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12726 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035772300507)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010586314070 + 2 * 0.737676 / 12726) := by gcongr
    _ ≤ (0.052430089979 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12726 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12726

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12726
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504741686 : ℝ) ≤ plow 12726 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12726) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702268117)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377456381) : eMP 12726 0.011 xi bn ≤ 0.001185889713 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12726 : ℝ) * (1 - 0.011))) ≤ 0.000586367354 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377456381 / (12726 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586367354 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586367354 : ℝ) + 3.141593 * 0.052702268117 / (12726 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185889713 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702268117)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377456381) : PiBarMP 12726 12 0.011 xi bn ≤ 0.161084276831 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12726 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037114099491 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.187405710266 : ℝ) ≤ √((12726 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.809574061778 : ℝ) ≤ √(12726 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12726) ≤ 0.123503775089 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037114099491 + 0.052702268117 * 1.772454 / (2 * (112.187405710266 : ℝ))) * (1 + 0.001185889713) +
        8 / (12726 * 112.809574061778) + 0.123503775089 := by gcongr
    _ ≤ (0.161084276831 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702268117)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377456381) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281999835628) :
    parallelOracle 12726 0.011 xi bn cd ≤ 0.162072328798 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12726 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12726 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504741686 : ℝ) ≤ plow 12726 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.809574061778 : ℝ) ≤ √(12726 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281999835628 : ℝ) / (2 * 0.560504741686 * 112.809574061778)) * 0.161084276831 +
        0.281999835628 ^ 2 / (2 * 0.560504741686 * 112.809574061778) := by gcongr
    _ ≤ (0.162072328798 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052702268117) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377456381)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281999835628) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12726 12726 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504741686 : ℝ) ≤ plow 12726 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.809574061778 : ℝ) ≤ √(12726 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12726 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12726 Θ 1.22 ≤ 0.011755212366 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.809574061778 := by gcongr <;> linarith
      _ ≤ (0.011755212366 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12726 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12726 12726 0.011 ≤ 0.008473456527 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12726 12726 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12726 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12726 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12726 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12726 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162072328798 + 0.011755212366 + (0.008473456527 : ℝ) *
        (1 + 2 * (0.281999835628 + 0.011755212366) / (0.560504741686 * 112.809574061778))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12726]

end BstLean.Part269.N12726

/-! The original eight local profiles supply actual 12726 moment certificates. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12726 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052702268117 ∧
    0 ≤ bN 12726 BstLean.Part154.csC (groupTheta g) ∧ bN 12726 BstLean.Part154.csC (groupTheta g) ≤ 0.001377456381 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12726 12726 0.011
      (momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12726 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12726 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12726 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229569745649 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12726 0.011
      (momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12726 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12726
/-! The actual computed-centre upper energy formula at 12726. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12726

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12726)
open BstLean.Part268 (cell12726)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085414795736
  | 2 => 0.086356166828
  | 3 => 0.087295477823
  | 4 => 0.088234100679
  | 5 => 0.089173696359
  | 6 => 0.090116257954
  | 7 => 0.091064157900
  | 8 => 0.092020199330
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12726 12726 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12726 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12726

/-! Actual upper energy certificates on all 43 source endpoints at 12726. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12726)
open BstLean.Part268 (cell12726)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12726 (gMinus 12726) (1 - (cell12726 i).lower) ≤ 1 ∧
    energyUpper 12726 (gMinus 12726) (BstLean.Part211.gPlus 12726)
      (finiteEnergy 12726 12726 0.011) (1 - (cell12726 i).lower) ≤
      (cell12726 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨10,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨11,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨12,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨13,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨14,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨15,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨16,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨17,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨18,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨19,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨20,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨21,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨22,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨23,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨24,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨25,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨26,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨27,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨28,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨29,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨30,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨31,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨32,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨33,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨34,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨35,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨36,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨37,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨38,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨39,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨40,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨41,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨42,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨43,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨44,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨45,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨46,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨47,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨48,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨49,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨50,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨51,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12726) (by norm_num)
        (q := 1 - (cell12726 ⟨52,by decide⟩).lower)
        (by norm_num [cell12726]) (by norm_num [cell12726])
      exact ⟨E.1,E.2.trans (by norm_num [cell12726])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12726

/-! Source-cell containment and simple scalar guards at 12726. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12726)
open BstLean.Part268 (cell12726)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12726 ⟨10,by decide⟩).lower ∧ (cell12726 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12726 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12726 ⟨11,by decide⟩).lower ∧ (cell12726 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12726 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12726 ⟨12,by decide⟩).lower ∧ (cell12726 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12726 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12726 ⟨13,by decide⟩).lower ∧ (cell12726 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12726 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12726 ⟨14,by decide⟩).lower ∧ (cell12726 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12726 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12726 ⟨15,by decide⟩).lower ∧ (cell12726 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12726 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12726 ⟨16,by decide⟩).lower ∧ (cell12726 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12726 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12726 ⟨17,by decide⟩).lower ∧ (cell12726 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12726 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12726 ⟨18,by decide⟩).lower ∧ (cell12726 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12726 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12726 ⟨19,by decide⟩).lower ∧ (cell12726 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12726 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12726 ⟨20,by decide⟩).lower ∧ (cell12726 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12726 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12726 ⟨21,by decide⟩).lower ∧ (cell12726 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12726 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12726 ⟨22,by decide⟩).lower ∧ (cell12726 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12726 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12726 ⟨23,by decide⟩).lower ∧ (cell12726 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12726 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12726 ⟨24,by decide⟩).lower ∧ (cell12726 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12726 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12726 ⟨25,by decide⟩).lower ∧ (cell12726 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12726 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12726 ⟨26,by decide⟩).lower ∧ (cell12726 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12726 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12726 ⟨27,by decide⟩).lower ∧ (cell12726 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12726 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12726 ⟨28,by decide⟩).lower ∧ (cell12726 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12726 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12726 ⟨29,by decide⟩).lower ∧ (cell12726 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12726 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12726 ⟨30,by decide⟩).lower ∧ (cell12726 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12726 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12726 ⟨31,by decide⟩).lower ∧ (cell12726 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12726 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12726 ⟨32,by decide⟩).lower ∧ (cell12726 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12726 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12726 ⟨33,by decide⟩).lower ∧ (cell12726 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12726 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12726 ⟨34,by decide⟩).lower ∧ (cell12726 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12726 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12726 ⟨35,by decide⟩).lower ∧ (cell12726 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12726 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12726 ⟨36,by decide⟩).lower ∧ (cell12726 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12726 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12726 ⟨37,by decide⟩).lower ∧ (cell12726 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12726 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12726 ⟨38,by decide⟩).lower ∧ (cell12726 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12726 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12726 ⟨39,by decide⟩).lower ∧ (cell12726 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12726 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12726 ⟨40,by decide⟩).lower ∧ (cell12726 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12726 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12726 ⟨41,by decide⟩).lower ∧ (cell12726 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12726 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12726 ⟨42,by decide⟩).lower ∧ (cell12726 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12726 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12726 ⟨43,by decide⟩).lower ∧ (cell12726 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12726 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12726 ⟨44,by decide⟩).lower ∧ (cell12726 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12726 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12726 ⟨45,by decide⟩).lower ∧ (cell12726 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12726 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12726 ⟨46,by decide⟩).lower ∧ (cell12726 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12726 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12726 ⟨47,by decide⟩).lower ∧ (cell12726 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12726 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12726 ⟨48,by decide⟩).lower ∧ (cell12726 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12726 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12726 ⟨49,by decide⟩).lower ∧ (cell12726 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12726 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12726 ⟨50,by decide⟩).lower ∧ (cell12726 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12726 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12726 ⟨51,by decide⟩).lower ∧ (cell12726 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12726 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12726 ⟨52,by decide⟩).lower ∧ (cell12726 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12726 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12726 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12726 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12726,cell12726,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12726 i).lower ∧
    (cell12726 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12726 i).upper ≤ (0.532 : ℝ) ∧
    (cell12726 i).centre ≤ (0.1 : ℝ) ∧ (cell12726 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12726 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12726 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12726

/-! The local source numeric instances at 12726 have no network premises. -/
namespace BstLean.Part269.N12726
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12726)
open BstLean.Part268 (cell12726)

noncomputable def sourceNumerics12726 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12726 (cell12726 i)
      scalarRow12726.M scalarRow12726.H scalarRow12726.xi := by
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
    energy_allowance := scalarRow12726.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12726]
    centre_nonneg := (scalarRow12726.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12726])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12726
/-! Actual 12727 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12727 ≤ (1.035770882761 : ℝ) := by
  have hr : (112.814006222631 : ℝ) ≤ √(12727 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.814006222631 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12727 12727 (11 / 1000) ≤
    (0.008473123625 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12727) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.814006222631 : ℝ) ≤ √(12727 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12727)
  have hdiv : K / √(12727 : ℝ) ≤ K / 112.814006222631 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.814006222631 ≤ (0.008473123625 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12727.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12727 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12727 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12727 := gPlus_lower 12727
end BstLean.Part269.N12727

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12727
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035770882760 : ℝ) ≤ wn 12727 := by
  have hn : √(12727 : ℝ) ≤ 112.814006222632 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12727 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.814006222632 ≤ 2 / √(12727 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251337207 : ℝ) ≤ rhoBar 12727 BstLean.Part154.csC ∧
    rhoBar 12727 BstLean.Part154.csC ≤ 0.000251337596 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035770882760 : ℝ) / (1.295212 * 12727) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035770882761 : ℝ) / (1.29521 * 12727) := by gcongr
      _ ≤ (0.000251337596 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12727 BstLean.Part154.csC) ≤ 0.001005413555 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12727 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) ≤ 0.000191973332 ∧
    cc1 (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) ≤ 0.000122153910 ∧
    cc2 (rhoBar 12727 BstLean.Part154.csC) ≤ 0.000070911285 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12727 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12727 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12727 BstLean.Part154.csC * nuR (rhoBar 12727 BstLean.Part154.csC)) ≤ 0.000502690985 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251337596 : ℝ) * 0.001005413555 := by gcongr
      _ ≤ (0.000502690985 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12727 BstLean.Part154.csC) * nuR (rhoBar 12727 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005413555 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12727 BstLean.Part154.csC) * rhoBar 12727 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251337596 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251337596 / 2 + 0.399 * 0.001005413555 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191973332 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502690985 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122153910 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251337596 / 1.414213562 := by gcongr
      _ ≤ (0.000070911285 : ℝ) := by norm_num

end BstLean.Part269.N12727

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12727
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) ≤ 1.59154E-7 := by
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12727 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12727 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12727 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191973332 : ℝ) ^ 2 + 0.000122153910 ^ 2 + 3 * 0.000070911285 ^ 2 +
        2 * 0.797885 * 0.000191973332 * 0.000122153910 + 2 * 0.000191973332 * 0.000070911285 +
        4 * 0.797885 * 0.000122153910 * 0.000070911285 := by gcongr
    _ ≤ (1.59154E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12727 BstLean.Part154.csC Θ ≤ 0.002623520506 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12727 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12727 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12727 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035770882761 * 1.59154E-7 / (0.000251337207 : ℝ) := by gcongr
    _ ≤ 0.002623520506 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12727 BstLean.Part154.csC Θ ≤ 0.002910825314 + 0.000662920364 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12727 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12727 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035770882761 : ℝ) * ((2 * Θ * 0.000251337596 +
        (6863 / 10000) * 0.000251337596 * 12727 * 0.001005413555) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002910825314 + 0.000662920364 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12727 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12727 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12727 0.011 Θ ∧ gammaRatio 12727 0.011 Θ ≤ 0.000086403366 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12727 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035770882761 : ℝ) * 0.525 / ((1 - 0.011) * 12727) := by gcongr
      _ ≤ (0.000086403366 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12727 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12727 0.011 Θ) :=
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
    badAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12727 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12727 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12727 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12727 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12727 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12727 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12727 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12727 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12727 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12727 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035770882761 : ℝ) * 12727 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003469909545 + 0.003286440870 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12727

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12727
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12727 BstLean.Part154.csC) (piBar (rhoBar 12727 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12727 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12727 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12727 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12727 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12727 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12727 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12727 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12727 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12727 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12727 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052428007829 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12727) ≤ 0.010585898162 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12727 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035770882761)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010585898162 + 2 * 0.737676 / 12727) := by gcongr
    _ ≤ (0.052428007829 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12727 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12727

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12727
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504786721 : ℝ) ≤ plow 12727 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12727) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701891002)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377348266) : eMP 12727 0.011 xi bn ≤ 0.001185796490 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12727 : ℝ) * (1 - 0.011))) ≤ 0.000586321306 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377348266 / (12727 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586321306 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586321306 : ℝ) + 3.141593 * 0.052701891002 / (12727 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185796490 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701891002)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377348266) : PiBarMP 12727 12 0.011 xi bn ≤ 0.161077942908 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12727 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037112642941 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.191813426827 : ℝ) ≤ √((12727 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.814006222631 : ℝ) ≤ √(12727 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12727) ≤ 0.123498922956 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037112642941 + 0.052701891002 * 1.772454 / (2 * (112.191813426827 : ℝ))) * (1 + 0.001185796490) +
        8 / (12727 * 112.814006222631) + 0.123498922956 := by gcongr
    _ ≤ (0.161077942908 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701891002)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377348266) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281996932125) :
    parallelOracle 12727 0.011 xi bn cd ≤ 0.162065925208 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12727 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12727 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504786721 : ℝ) ≤ plow 12727 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.814006222631 : ℝ) ≤ √(12727 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281996932125 : ℝ) / (2 * 0.560504786721 * 112.814006222631)) * 0.161077942908 +
        0.281996932125 ^ 2 / (2 * 0.560504786721 * 112.814006222631) := by gcongr
    _ ≤ (0.162065925208 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701891002) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377348266)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281996932125) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12727 12727 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504786721 : ℝ) ≤ plow 12727 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.814006222631 : ℝ) ≤ √(12727 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12727 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12727 Θ 1.22 ≤ 0.011754750535 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.814006222631 := by gcongr <;> linarith
      _ ≤ (0.011754750535 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12727 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12727 12727 0.011 ≤ 0.008473123625 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12727 12727 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12727 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12727 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12727 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12727 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162065925208 + 0.011754750535 + (0.008473123625 : ℝ) *
        (1 + 2 * (0.281996932125 + 0.011754750535) / (0.560504786721 * 112.814006222631))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12727]

end BstLean.Part269.N12727

/-! The original eight local profiles supply actual 12727 moment certificates. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12727 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052701891002 ∧
    0 ≤ bN 12727 BstLean.Part154.csC (groupTheta g) ∧ bN 12727 BstLean.Part154.csC (groupTheta g) ≤ 0.001377348266 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12727 12727 0.011
      (momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12727 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12727 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12727 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229568924296 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12727 0.011
      (momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12727 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12727
/-! The actual computed-centre upper energy formula at 12727. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12727

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12727)
open BstLean.Part268 (cell12727)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085411907784
  | 2 => 0.086353226457
  | 3 => 0.087292477489
  | 4 => 0.088231031093
  | 5 => 0.089170546177
  | 6 => 0.090113013431
  | 7 => 0.091060802499
  | 8 => 0.092016713290
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12727 12727 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12727 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12727

/-! Actual upper energy certificates on all 43 source endpoints at 12727. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12727)
open BstLean.Part268 (cell12727)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12727 (gMinus 12727) (1 - (cell12727 i).lower) ≤ 1 ∧
    energyUpper 12727 (gMinus 12727) (BstLean.Part211.gPlus 12727)
      (finiteEnergy 12727 12727 0.011) (1 - (cell12727 i).lower) ≤
      (cell12727 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨10,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨11,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨12,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨13,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨14,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨15,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨16,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨17,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨18,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨19,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨20,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨21,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨22,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨23,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨24,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨25,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨26,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨27,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨28,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨29,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨30,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨31,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨32,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨33,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨34,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨35,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨36,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨37,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨38,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨39,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨40,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨41,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨42,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨43,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨44,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨45,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨46,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨47,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨48,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨49,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨50,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨51,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12727) (by norm_num)
        (q := 1 - (cell12727 ⟨52,by decide⟩).lower)
        (by norm_num [cell12727]) (by norm_num [cell12727])
      exact ⟨E.1,E.2.trans (by norm_num [cell12727])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12727

/-! Source-cell containment and simple scalar guards at 12727. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12727)
open BstLean.Part268 (cell12727)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12727 ⟨10,by decide⟩).lower ∧ (cell12727 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12727 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12727 ⟨11,by decide⟩).lower ∧ (cell12727 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12727 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12727 ⟨12,by decide⟩).lower ∧ (cell12727 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12727 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12727 ⟨13,by decide⟩).lower ∧ (cell12727 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12727 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12727 ⟨14,by decide⟩).lower ∧ (cell12727 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12727 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12727 ⟨15,by decide⟩).lower ∧ (cell12727 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12727 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12727 ⟨16,by decide⟩).lower ∧ (cell12727 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12727 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12727 ⟨17,by decide⟩).lower ∧ (cell12727 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12727 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12727 ⟨18,by decide⟩).lower ∧ (cell12727 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12727 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12727 ⟨19,by decide⟩).lower ∧ (cell12727 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12727 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12727 ⟨20,by decide⟩).lower ∧ (cell12727 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12727 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12727 ⟨21,by decide⟩).lower ∧ (cell12727 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12727 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12727 ⟨22,by decide⟩).lower ∧ (cell12727 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12727 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12727 ⟨23,by decide⟩).lower ∧ (cell12727 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12727 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12727 ⟨24,by decide⟩).lower ∧ (cell12727 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12727 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12727 ⟨25,by decide⟩).lower ∧ (cell12727 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12727 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12727 ⟨26,by decide⟩).lower ∧ (cell12727 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12727 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12727 ⟨27,by decide⟩).lower ∧ (cell12727 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12727 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12727 ⟨28,by decide⟩).lower ∧ (cell12727 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12727 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12727 ⟨29,by decide⟩).lower ∧ (cell12727 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12727 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12727 ⟨30,by decide⟩).lower ∧ (cell12727 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12727 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12727 ⟨31,by decide⟩).lower ∧ (cell12727 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12727 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12727 ⟨32,by decide⟩).lower ∧ (cell12727 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12727 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12727 ⟨33,by decide⟩).lower ∧ (cell12727 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12727 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12727 ⟨34,by decide⟩).lower ∧ (cell12727 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12727 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12727 ⟨35,by decide⟩).lower ∧ (cell12727 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12727 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12727 ⟨36,by decide⟩).lower ∧ (cell12727 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12727 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12727 ⟨37,by decide⟩).lower ∧ (cell12727 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12727 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12727 ⟨38,by decide⟩).lower ∧ (cell12727 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12727 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12727 ⟨39,by decide⟩).lower ∧ (cell12727 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12727 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12727 ⟨40,by decide⟩).lower ∧ (cell12727 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12727 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12727 ⟨41,by decide⟩).lower ∧ (cell12727 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12727 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12727 ⟨42,by decide⟩).lower ∧ (cell12727 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12727 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12727 ⟨43,by decide⟩).lower ∧ (cell12727 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12727 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12727 ⟨44,by decide⟩).lower ∧ (cell12727 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12727 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12727 ⟨45,by decide⟩).lower ∧ (cell12727 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12727 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12727 ⟨46,by decide⟩).lower ∧ (cell12727 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12727 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12727 ⟨47,by decide⟩).lower ∧ (cell12727 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12727 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12727 ⟨48,by decide⟩).lower ∧ (cell12727 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12727 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12727 ⟨49,by decide⟩).lower ∧ (cell12727 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12727 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12727 ⟨50,by decide⟩).lower ∧ (cell12727 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12727 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12727 ⟨51,by decide⟩).lower ∧ (cell12727 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12727 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12727 ⟨52,by decide⟩).lower ∧ (cell12727 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12727 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12727 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12727 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12727,cell12727,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12727 i).lower ∧
    (cell12727 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12727 i).upper ≤ (0.532 : ℝ) ∧
    (cell12727 i).centre ≤ (0.1 : ℝ) ∧ (cell12727 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12727 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12727 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12727

/-! The local source numeric instances at 12727 have no network premises. -/
namespace BstLean.Part269.N12727
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12727)
open BstLean.Part268 (cell12727)

noncomputable def sourceNumerics12727 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12727 (cell12727 i)
      scalarRow12727.M scalarRow12727.H scalarRow12727.xi := by
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
    energy_allowance := scalarRow12727.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12727]
    centre_nonneg := (scalarRow12727.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12727])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12727
/-! Actual 12728 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12728 ≤ (1.035769465183 : ℝ) := by
  have hr : (112.818438209363 : ℝ) ≤ √(12728 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.818438209363 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12728 12728 (11 / 1000) ≤
    (0.008472790762 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12728) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.818438209363 : ℝ) ≤ √(12728 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12728)
  have hdiv : K / √(12728 : ℝ) ≤ K / 112.818438209363 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.818438209363 ≤ (0.008472790762 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12728.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12728 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12728 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12728 := gPlus_lower 12728
end BstLean.Part269.N12728

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12728
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035769465182 : ℝ) ≤ wn 12728 := by
  have hn : √(12728 : ℝ) ≤ 112.818438209364 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12728 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.818438209364 ≤ 2 / √(12728 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251317116 : ℝ) ≤ rhoBar 12728 BstLean.Part154.csC ∧
    rhoBar 12728 BstLean.Part154.csC ≤ 0.000251317506 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035769465182 : ℝ) / (1.295212 * 12728) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035769465183 : ℝ) / (1.29521 * 12728) := by gcongr
      _ ≤ (0.000251317506 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12728 BstLean.Part154.csC) ≤ 0.001005333185 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12728 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) ≤ 0.000191957987 ∧
    cc1 (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) ≤ 0.000122144146 ∧
    cc2 (rhoBar 12728 BstLean.Part154.csC) ≤ 0.000070905617 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12728 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12728 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12728 BstLean.Part154.csC * nuR (rhoBar 12728 BstLean.Part154.csC)) ≤ 0.000502650803 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251317506 : ℝ) * 0.001005333185 := by gcongr
      _ ≤ (0.000502650803 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12728 BstLean.Part154.csC) * nuR (rhoBar 12728 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005333185 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12728 BstLean.Part154.csC) * rhoBar 12728 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251317506 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251317506 / 2 + 0.399 * 0.001005333185 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191957987 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502650803 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122144146 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251317506 / 1.414213562 := by gcongr
      _ ≤ (0.000070905617 : ℝ) := by norm_num

end BstLean.Part269.N12728

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12728
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) ≤ 1.59128E-7 := by
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12728 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12728 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12728 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191957987 : ℝ) ^ 2 + 0.000122144146 ^ 2 + 3 * 0.000070905617 ^ 2 +
        2 * 0.797885 * 0.000191957987 * 0.000122144146 + 2 * 0.000191957987 * 0.000070905617 +
        4 * 0.797885 * 0.000122144146 * 0.000070905617 := by gcongr
    _ ≤ (1.59128E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12728 BstLean.Part154.csC Θ ≤ 0.002623298025 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12728 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12728 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12728 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035769465183 * 1.59128E-7 / (0.000251317116 : ℝ) := by gcongr
    _ ≤ 0.002623298025 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12728 BstLean.Part154.csC Θ ≤ 0.002910584673 + 0.000662866468 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12728 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12728 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035769465183 : ℝ) * ((2 * Θ * 0.000251317506 +
        (6863 / 10000) * 0.000251317506 * 12728 * 0.001005333185) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002910584673 + 0.000662866468 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12728 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12728 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12728 0.011 Θ ∧ gammaRatio 12728 0.011 Θ ≤ 0.000086396460 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12728 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035769465183 : ℝ) * 0.525 / ((1 - 0.011) * 12728) := by gcongr
      _ ≤ (0.000086396460 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12728 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12728 0.011 Θ) :=
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
    badAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12728 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12728 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12728 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12728 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12728 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12728 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12728 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12728 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12728 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12728 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035769465183 : ℝ) * 12728 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003469668904 + 0.003286164493 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12728

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12728
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12728 BstLean.Part154.csC) (piBar (rhoBar 12728 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12728 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12728 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12728 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12728 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12728 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12728 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12728 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12728 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12728 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12728 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052425925925 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12728) ≤ 0.010585482303 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12728 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035769465183)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010585482303 + 2 * 0.737676 / 12728) := by gcongr
    _ ≤ (0.052425925925 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12728 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12728

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12728
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504831748 : ℝ) ≤ plow 12728 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12728) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701505263)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377231464) : eMP 12728 0.011 xi bn ≤ 0.001185699574 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12728 : ℝ) * (1 - 0.011))) ≤ 0.000586273413 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377231464 / (12728 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586273413 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586273413 : ℝ) + 3.141593 * 0.052701505263 / (12728 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185699574 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701505263)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377231464) : PiBarMP 12728 12 0.011 xi bn ≤ 0.161071492114 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12728 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037111069293 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.196220970226 : ℝ) ≤ √((12728 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.818438209363 : ℝ) ≤ √(12728 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12728) ≤ 0.123494071394 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037111069293 + 0.052701505263 * 1.772454 / (2 * (112.196220970226 : ℝ))) * (1 + 0.001185699574) +
        8 / (12728 * 112.818438209363) + 0.123494071394 := by gcongr
    _ ≤ (0.161071492114 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701505263)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377231464) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281994010081) :
    parallelOracle 12728 0.011 xi bn cd ≤ 0.162059404386 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12728 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12728 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504831748 : ℝ) ≤ plow 12728 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.818438209363 : ℝ) ≤ √(12728 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281994010081 : ℝ) / (2 * 0.560504831748 * 112.818438209363)) * 0.161071492114 +
        0.281994010081 ^ 2 / (2 * 0.560504831748 * 112.818438209363) := by gcongr
    _ ≤ (0.162059404386 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701505263) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377231464)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281994010081) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12728 12728 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504831748 : ℝ) ≤ plow 12728 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.818438209363 : ℝ) ≤ √(12728 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12728 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12728 Θ 1.22 ≤ 0.011754288759 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.818438209363 := by gcongr <;> linarith
      _ ≤ (0.011754288759 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12728 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12728 12728 0.011 ≤ 0.008472790762 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12728 12728 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12728 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12728 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12728 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12728 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162059404386 + 0.011754288759 + (0.008472790762 : ℝ) *
        (1 + 2 * (0.281994010081 + 0.011754288759) / (0.560504831748 * 112.818438209363))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12728]

end BstLean.Part269.N12728

/-! The original eight local profiles supply actual 12728 moment certificates. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12728 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052701505263 ∧
    0 ≤ bN 12728 BstLean.Part154.csC (groupTheta g) ∧ bN 12728 BstLean.Part154.csC (groupTheta g) ≤ 0.001377231464 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12728 12728 0.011
      (momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12728 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12728 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12728 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229568084156 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12728 0.011
      (momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12728 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12728
/-! The actual computed-centre upper energy formula at 12728. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12728

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12728)
open BstLean.Part268 (cell12728)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085409020888
  | 2 => 0.086350287184
  | 3 => 0.087289478306
  | 4 => 0.088227962723
  | 5 => 0.089167397291
  | 6 => 0.090109770301
  | 7 => 0.091057448608
  | 8 => 0.092013228901
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12728 12728 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12728 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12728

/-! Actual upper energy certificates on all 43 source endpoints at 12728. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12728)
open BstLean.Part268 (cell12728)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12728 (gMinus 12728) (1 - (cell12728 i).lower) ≤ 1 ∧
    energyUpper 12728 (gMinus 12728) (BstLean.Part211.gPlus 12728)
      (finiteEnergy 12728 12728 0.011) (1 - (cell12728 i).lower) ≤
      (cell12728 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨10,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨11,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨12,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨13,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨14,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨15,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨16,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨17,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨18,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨19,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨20,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨21,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨22,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨23,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨24,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨25,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨26,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨27,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨28,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨29,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨30,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨31,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨32,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨33,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨34,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨35,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨36,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨37,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨38,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨39,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨40,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨41,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨42,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨43,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨44,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨45,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨46,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨47,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨48,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨49,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨50,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨51,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12728) (by norm_num)
        (q := 1 - (cell12728 ⟨52,by decide⟩).lower)
        (by norm_num [cell12728]) (by norm_num [cell12728])
      exact ⟨E.1,E.2.trans (by norm_num [cell12728])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12728

/-! Source-cell containment and simple scalar guards at 12728. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12728)
open BstLean.Part268 (cell12728)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12728 ⟨10,by decide⟩).lower ∧ (cell12728 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12728 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12728 ⟨11,by decide⟩).lower ∧ (cell12728 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12728 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12728 ⟨12,by decide⟩).lower ∧ (cell12728 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12728 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12728 ⟨13,by decide⟩).lower ∧ (cell12728 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12728 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12728 ⟨14,by decide⟩).lower ∧ (cell12728 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12728 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12728 ⟨15,by decide⟩).lower ∧ (cell12728 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12728 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12728 ⟨16,by decide⟩).lower ∧ (cell12728 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12728 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12728 ⟨17,by decide⟩).lower ∧ (cell12728 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12728 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12728 ⟨18,by decide⟩).lower ∧ (cell12728 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12728 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12728 ⟨19,by decide⟩).lower ∧ (cell12728 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12728 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12728 ⟨20,by decide⟩).lower ∧ (cell12728 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12728 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12728 ⟨21,by decide⟩).lower ∧ (cell12728 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12728 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12728 ⟨22,by decide⟩).lower ∧ (cell12728 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12728 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12728 ⟨23,by decide⟩).lower ∧ (cell12728 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12728 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12728 ⟨24,by decide⟩).lower ∧ (cell12728 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12728 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12728 ⟨25,by decide⟩).lower ∧ (cell12728 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12728 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12728 ⟨26,by decide⟩).lower ∧ (cell12728 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12728 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12728 ⟨27,by decide⟩).lower ∧ (cell12728 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12728 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12728 ⟨28,by decide⟩).lower ∧ (cell12728 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12728 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12728 ⟨29,by decide⟩).lower ∧ (cell12728 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12728 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12728 ⟨30,by decide⟩).lower ∧ (cell12728 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12728 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12728 ⟨31,by decide⟩).lower ∧ (cell12728 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12728 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12728 ⟨32,by decide⟩).lower ∧ (cell12728 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12728 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12728 ⟨33,by decide⟩).lower ∧ (cell12728 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12728 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12728 ⟨34,by decide⟩).lower ∧ (cell12728 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12728 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12728 ⟨35,by decide⟩).lower ∧ (cell12728 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12728 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12728 ⟨36,by decide⟩).lower ∧ (cell12728 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12728 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12728 ⟨37,by decide⟩).lower ∧ (cell12728 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12728 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12728 ⟨38,by decide⟩).lower ∧ (cell12728 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12728 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12728 ⟨39,by decide⟩).lower ∧ (cell12728 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12728 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12728 ⟨40,by decide⟩).lower ∧ (cell12728 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12728 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12728 ⟨41,by decide⟩).lower ∧ (cell12728 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12728 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12728 ⟨42,by decide⟩).lower ∧ (cell12728 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12728 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12728 ⟨43,by decide⟩).lower ∧ (cell12728 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12728 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12728 ⟨44,by decide⟩).lower ∧ (cell12728 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12728 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12728 ⟨45,by decide⟩).lower ∧ (cell12728 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12728 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12728 ⟨46,by decide⟩).lower ∧ (cell12728 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12728 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12728 ⟨47,by decide⟩).lower ∧ (cell12728 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12728 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12728 ⟨48,by decide⟩).lower ∧ (cell12728 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12728 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12728 ⟨49,by decide⟩).lower ∧ (cell12728 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12728 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12728 ⟨50,by decide⟩).lower ∧ (cell12728 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12728 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12728 ⟨51,by decide⟩).lower ∧ (cell12728 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12728 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12728 ⟨52,by decide⟩).lower ∧ (cell12728 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12728 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12728 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12728 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12728,cell12728,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12728 i).lower ∧
    (cell12728 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12728 i).upper ≤ (0.532 : ℝ) ∧
    (cell12728 i).centre ≤ (0.1 : ℝ) ∧ (cell12728 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12728 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12728 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12728

/-! The local source numeric instances at 12728 have no network premises. -/
namespace BstLean.Part269.N12728
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12728)
open BstLean.Part268 (cell12728)

noncomputable def sourceNumerics12728 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12728 (cell12728 i)
      scalarRow12728.M scalarRow12728.H scalarRow12728.xi := by
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
    energy_allowance := scalarRow12728.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12728]
    centre_nonneg := (scalarRow12728.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12728])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12728
/-! Actual 12729 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12729 ≤ (1.035768047772 : ℝ) := by
  have hr : (112.822870021995 : ℝ) ≤ √(12729 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.822870021995 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12729 12729 (11 / 1000) ≤
    (0.008472457938 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12729) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.822870021995 : ℝ) ≤ √(12729 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12729)
  have hdiv : K / √(12729 : ℝ) ≤ K / 112.822870021995 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.822870021995 ≤ (0.008472457938 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12729.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12729 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12729 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12729 := gPlus_lower 12729
end BstLean.Part269.N12729

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12729
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035768047771 : ℝ) ≤ wn 12729 := by
  have hn : √(12729 : ℝ) ≤ 112.822870021996 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12729 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.822870021996 ≤ 2 / √(12729 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251297029 : ℝ) ≤ rhoBar 12729 BstLean.Part154.csC ∧
    rhoBar 12729 BstLean.Part154.csC ≤ 0.000251297418 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035768047771 : ℝ) / (1.295212 * 12729) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035768047772 : ℝ) / (1.29521 * 12729) := by gcongr
      _ ≤ (0.000251297418 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12729 BstLean.Part154.csC) ≤ 0.001005252823 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12729 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) ≤ 0.000191942642 ∧
    cc1 (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) ≤ 0.000122134382 ∧
    cc2 (rhoBar 12729 BstLean.Part154.csC) ≤ 0.000070899950 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12729 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12729 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12729 BstLean.Part154.csC * nuR (rhoBar 12729 BstLean.Part154.csC)) ≤ 0.000502610624 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251297418 : ℝ) * 0.001005252823 := by gcongr
      _ ≤ (0.000502610624 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12729 BstLean.Part154.csC) * nuR (rhoBar 12729 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005252823 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12729 BstLean.Part154.csC) * rhoBar 12729 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251297418 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251297418 / 2 + 0.399 * 0.001005252823 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191942642 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502610624 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122134382 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251297418 / 1.414213562 := by gcongr
      _ ≤ (0.000070899950 : ℝ) := by norm_num

end BstLean.Part269.N12729

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12729
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) ≤ 1.59103E-7 := by
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12729 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12729 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12729 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191942642 : ℝ) ^ 2 + 0.000122134382 ^ 2 + 3 * 0.000070899950 ^ 2 +
        2 * 0.797885 * 0.000191942642 * 0.000122134382 + 2 * 0.000191942642 * 0.000070899950 +
        4 * 0.797885 * 0.000122134382 * 0.000070899950 := by gcongr
    _ ≤ (1.59103E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12729 BstLean.Part154.csC Θ ≤ 0.002623091954 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12729 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12729 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12729 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035768047772 * 1.59103E-7 / (0.000251297029 : ℝ) := by gcongr
    _ ≤ 0.002623091954 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12729 BstLean.Part154.csC Θ ≤ 0.002910344043 + 0.000662812577 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12729 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12729 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035768047772 : ℝ) * ((2 * Θ * 0.000251297418 +
        (6863 / 10000) * 0.000251297418 * 12729 * 0.001005252823) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002910344043 + 0.000662812577 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12729 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12729 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12729 0.011 Θ ∧ gammaRatio 12729 0.011 Θ ≤ 0.000086389554 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12729 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035768047772 : ℝ) * 0.525 / ((1 - 0.011) * 12729) := by gcongr
      _ ≤ (0.000086389554 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12729 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12729 0.011 Θ) :=
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
    badAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12729 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12729 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12729 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12729 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12729 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12729 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12729 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12729 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12729 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12729 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035768047772 : ℝ) * 12729 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003469428274 + 0.003285904531 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12729

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12729
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12729 BstLean.Part154.csC) (piBar (rhoBar 12729 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12729 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12729 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12729 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12729 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12729 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12729 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12729 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12729 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12729 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12729 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052423844269 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12729) ≤ 0.010585066493 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12729 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035768047772)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010585066493 + 2 * 0.737676 / 12729) := by gcongr
    _ ≤ (0.052423844269 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12729 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12729

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12729
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504876769 : ℝ) ≤ plow 12729 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12729) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701128153)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377123276) : eMP 12729 0.011 xi bn ≤ 0.001185606333 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12729 : ℝ) * (1 - 0.011))) ≤ 0.000586227356 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377123276 / (12729 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586227356 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586227356 : ℝ) + 3.141593 * 0.052701128153 / (12729 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185606333 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701128153)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377123276) : PiBarMP 12729 12 0.011 xi bn ≤ 0.161065158233 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12729 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037109611640 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.200628340486 : ℝ) ≤ √((12729 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.822870021995 : ℝ) ≤ √(12729 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12729) ≤ 0.123489220404 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037109611640 + 0.052701128153 * 1.772454 / (2 * (112.200628340486 : ℝ))) * (1 + 0.001185606333) +
        8 / (12729 * 112.822870021995) + 0.123489220404 := by gcongr
    _ ≤ (0.161065158233 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701128153)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377123276) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281991107077) :
    parallelOracle 12729 0.011 xi bn cd ≤ 0.162053000855 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12729 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12729 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504876769 : ℝ) ≤ plow 12729 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.822870021995 : ℝ) ≤ √(12729 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281991107077 : ℝ) / (2 * 0.560504876769 * 112.822870021995)) * 0.161065158233 +
        0.281991107077 ^ 2 / (2 * 0.560504876769 * 112.822870021995) := by gcongr
    _ ≤ (0.162053000855 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052701128153) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377123276)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281991107077) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12729 12729 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504876769 : ℝ) ≤ plow 12729 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.822870021995 : ℝ) ≤ √(12729 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12729 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12729 Θ 1.22 ≤ 0.011753827037 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.822870021995 := by gcongr <;> linarith
      _ ≤ (0.011753827037 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12729 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12729 12729 0.011 ≤ 0.008472457938 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12729 12729 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12729 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12729 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12729 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12729 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162053000855 + 0.011753827037 + (0.008472457938 : ℝ) *
        (1 + 2 * (0.281991107077 + 0.011753827037) / (0.560504876769 * 112.822870021995))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12729]

end BstLean.Part269.N12729

/-! The original eight local profiles supply actual 12729 moment certificates. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12729 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052701128153 ∧
    0 ≤ bN 12729 BstLean.Part154.csC (groupTheta g) ∧ bN 12729 BstLean.Part154.csC (groupTheta g) ≤ 0.001377123276 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12729 12729 0.011
      (momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12729 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12729 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12729 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229567262808 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12729 0.011
      (momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12729 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12729
/-! The actual computed-centre upper energy formula at 12729. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12729

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12729)
open BstLean.Part268 (cell12729)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085406135045
  | 2 => 0.086347349007
  | 3 => 0.087286480272
  | 4 => 0.088224895567
  | 5 => 0.089164249699
  | 6 => 0.090106528562
  | 7 => 0.091054096225
  | 8 => 0.092009746162
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12729 12729 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12729 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12729

/-! Actual upper energy certificates on all 43 source endpoints at 12729. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12729)
open BstLean.Part268 (cell12729)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12729 (gMinus 12729) (1 - (cell12729 i).lower) ≤ 1 ∧
    energyUpper 12729 (gMinus 12729) (BstLean.Part211.gPlus 12729)
      (finiteEnergy 12729 12729 0.011) (1 - (cell12729 i).lower) ≤
      (cell12729 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨10,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨11,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨12,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨13,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨14,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨15,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨16,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨17,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨18,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨19,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨20,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨21,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨22,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨23,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨24,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨25,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨26,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨27,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨28,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨29,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨30,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨31,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨32,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨33,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨34,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨35,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨36,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨37,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨38,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨39,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨40,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨41,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨42,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨43,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨44,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨45,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨46,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨47,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨48,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨49,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨50,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨51,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12729) (by norm_num)
        (q := 1 - (cell12729 ⟨52,by decide⟩).lower)
        (by norm_num [cell12729]) (by norm_num [cell12729])
      exact ⟨E.1,E.2.trans (by norm_num [cell12729])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12729

/-! Source-cell containment and simple scalar guards at 12729. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12729)
open BstLean.Part268 (cell12729)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12729 ⟨10,by decide⟩).lower ∧ (cell12729 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12729 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12729 ⟨11,by decide⟩).lower ∧ (cell12729 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12729 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12729 ⟨12,by decide⟩).lower ∧ (cell12729 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12729 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12729 ⟨13,by decide⟩).lower ∧ (cell12729 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12729 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12729 ⟨14,by decide⟩).lower ∧ (cell12729 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12729 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12729 ⟨15,by decide⟩).lower ∧ (cell12729 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12729 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12729 ⟨16,by decide⟩).lower ∧ (cell12729 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12729 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12729 ⟨17,by decide⟩).lower ∧ (cell12729 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12729 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12729 ⟨18,by decide⟩).lower ∧ (cell12729 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12729 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12729 ⟨19,by decide⟩).lower ∧ (cell12729 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12729 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12729 ⟨20,by decide⟩).lower ∧ (cell12729 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12729 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12729 ⟨21,by decide⟩).lower ∧ (cell12729 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12729 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12729 ⟨22,by decide⟩).lower ∧ (cell12729 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12729 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12729 ⟨23,by decide⟩).lower ∧ (cell12729 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12729 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12729 ⟨24,by decide⟩).lower ∧ (cell12729 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12729 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12729 ⟨25,by decide⟩).lower ∧ (cell12729 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12729 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12729 ⟨26,by decide⟩).lower ∧ (cell12729 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12729 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12729 ⟨27,by decide⟩).lower ∧ (cell12729 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12729 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12729 ⟨28,by decide⟩).lower ∧ (cell12729 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12729 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12729 ⟨29,by decide⟩).lower ∧ (cell12729 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12729 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12729 ⟨30,by decide⟩).lower ∧ (cell12729 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12729 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12729 ⟨31,by decide⟩).lower ∧ (cell12729 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12729 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12729 ⟨32,by decide⟩).lower ∧ (cell12729 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12729 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12729 ⟨33,by decide⟩).lower ∧ (cell12729 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12729 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12729 ⟨34,by decide⟩).lower ∧ (cell12729 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12729 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12729 ⟨35,by decide⟩).lower ∧ (cell12729 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12729 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12729 ⟨36,by decide⟩).lower ∧ (cell12729 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12729 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12729 ⟨37,by decide⟩).lower ∧ (cell12729 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12729 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12729 ⟨38,by decide⟩).lower ∧ (cell12729 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12729 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12729 ⟨39,by decide⟩).lower ∧ (cell12729 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12729 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12729 ⟨40,by decide⟩).lower ∧ (cell12729 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12729 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12729 ⟨41,by decide⟩).lower ∧ (cell12729 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12729 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12729 ⟨42,by decide⟩).lower ∧ (cell12729 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12729 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12729 ⟨43,by decide⟩).lower ∧ (cell12729 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12729 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12729 ⟨44,by decide⟩).lower ∧ (cell12729 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12729 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12729 ⟨45,by decide⟩).lower ∧ (cell12729 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12729 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12729 ⟨46,by decide⟩).lower ∧ (cell12729 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12729 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12729 ⟨47,by decide⟩).lower ∧ (cell12729 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12729 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12729 ⟨48,by decide⟩).lower ∧ (cell12729 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12729 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12729 ⟨49,by decide⟩).lower ∧ (cell12729 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12729 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12729 ⟨50,by decide⟩).lower ∧ (cell12729 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12729 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12729 ⟨51,by decide⟩).lower ∧ (cell12729 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12729 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12729 ⟨52,by decide⟩).lower ∧ (cell12729 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12729 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12729 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12729 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12729,cell12729,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12729 i).lower ∧
    (cell12729 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12729 i).upper ≤ (0.532 : ℝ) ∧
    (cell12729 i).centre ≤ (0.1 : ℝ) ∧ (cell12729 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12729 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12729 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12729

/-! The local source numeric instances at 12729 have no network premises. -/
namespace BstLean.Part269.N12729
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12729)
open BstLean.Part268 (cell12729)

noncomputable def sourceNumerics12729 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12729 (cell12729 i)
      scalarRow12729.M scalarRow12729.H scalarRow12729.xi := by
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
    energy_allowance := scalarRow12729.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12729]
    centre_nonneg := (scalarRow12729.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12729])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12729
/-! Actual 12730 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12730 ≤ (1.035766630530 : ℝ) := by
  have hr : (112.827301660546 : ℝ) ≤ √(12730 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.827301660546 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12730 12730 (11 / 1000) ≤
    (0.008472125154 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12730) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.827301660546 : ℝ) ≤ √(12730 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12730)
  have hdiv : K / √(12730 : ℝ) ≤ K / 112.827301660546 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.827301660546 ≤ (0.008472125154 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12730.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12730 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12730 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12730 := gPlus_lower 12730
end BstLean.Part269.N12730

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12730
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035766630529 : ℝ) ≤ wn 12730 := by
  have hn : √(12730 : ℝ) ≤ 112.827301660547 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12730 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.827301660547 ≤ 2 / √(12730 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251276945 : ℝ) ≤ rhoBar 12730 BstLean.Part154.csC ∧
    rhoBar 12730 BstLean.Part154.csC ≤ 0.000251277334 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035766630529 : ℝ) / (1.295212 * 12730) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035766630530 : ℝ) / (1.29521 * 12730) := by gcongr
      _ ≤ (0.000251277334 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12730 BstLean.Part154.csC) ≤ 0.001005172477 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12730 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) ≤ 0.000191927301 ∧
    cc1 (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) ≤ 0.000122124621 ∧
    cc2 (rhoBar 12730 BstLean.Part154.csC) ≤ 0.000070894283 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12730 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12730 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12730 BstLean.Part154.csC * nuR (rhoBar 12730 BstLean.Part154.csC)) ≤ 0.000502570454 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251277334 : ℝ) * 0.001005172477 := by gcongr
      _ ≤ (0.000502570454 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12730 BstLean.Part154.csC) * nuR (rhoBar 12730 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005172477 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12730 BstLean.Part154.csC) * rhoBar 12730 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251277334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251277334 / 2 + 0.399 * 0.001005172477 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191927301 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502570454 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122124621 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251277334 / 1.414213562 := by gcongr
      _ ≤ (0.000070894283 : ℝ) := by norm_num

end BstLean.Part269.N12730

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12730
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) ≤ 1.59078E-7 := by
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12730 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12730 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12730 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191927301 : ℝ) ^ 2 + 0.000122124621 ^ 2 + 3 * 0.000070894283 ^ 2 +
        2 * 0.797885 * 0.000191927301 * 0.000122124621 + 2 * 0.000191927301 * 0.000070894283 +
        4 * 0.797885 * 0.000122124621 * 0.000070894283 := by gcongr
    _ ≤ (1.59078E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12730 BstLean.Part154.csC Θ ≤ 0.002622885822 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12730 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12730 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12730 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035766630530 * 1.59078E-7 / (0.000251276945 : ℝ) := by gcongr
    _ ≤ 0.002622885822 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12730 BstLean.Part154.csC Θ ≤ 0.002910103471 + 0.000662758698 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12730 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12730 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035766630530 : ℝ) * ((2 * Θ * 0.000251277334 +
        (6863 / 10000) * 0.000251277334 * 12730 * 0.001005172477) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002910103471 + 0.000662758698 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12730 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12730 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12730 0.011 Θ ∧ gammaRatio 12730 0.011 Θ ≤ 0.000086382650 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12730 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035766630530 : ℝ) * 0.525 / ((1 - 0.011) * 12730) := by gcongr
      _ ≤ (0.000086382650 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12730 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12730 0.011 Θ) :=
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
    badAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12730 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12730 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12730 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12730 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12730 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12730 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12730 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12730 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12730 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12730 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035766630530 : ℝ) * 12730 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003469187702 + 0.003285644520 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12730

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12730
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12730 BstLean.Part154.csC) (piBar (rhoBar 12730 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12730 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12730 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12730 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12730 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12730 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12730 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12730 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12730 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12730 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12730 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052421762859 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12730) ≤ 0.010584650732 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12730 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035766630530)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010584650732 + 2 * 0.737676 / 12730) := by gcongr
    _ ≤ (0.052421762859 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12730 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12730

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12730
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504921783 : ℝ) ≤ plow 12730 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12730) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700751075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377015057) : eMP 12730 0.011 xi bn ≤ 0.001185513087 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12730 : ℝ) * (1 - 0.011))) ≤ 0.000586181297 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377015057 / (12730 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586181297 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586181297 : ℝ) + 3.141593 * 0.052700751075 / (12730 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185513087 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700751075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377015057) : PiBarMP 12730 12 0.011 xi bn ≤ 0.161058824452 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12730 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037108153512 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.205035537626 : ℝ) ≤ √((12730 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.827301660546 : ℝ) ≤ √(12730 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12730) ≤ 0.123484369986 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037108153512 + 0.052700751075 * 1.772454 / (2 * (112.205035537626 : ℝ))) * (1 + 0.001185513087) +
        8 / (12730 * 112.827301660546) + 0.123484369986 := by gcongr
    _ ≤ (0.161058824452 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700751075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377015057) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281988204386) :
    parallelOracle 12730 0.011 xi bn cd ≤ 0.162046597434 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12730 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12730 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504921783 : ℝ) ≤ plow 12730 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.827301660546 : ℝ) ≤ √(12730 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281988204386 : ℝ) / (2 * 0.560504921783 * 112.827301660546)) * 0.161058824452 +
        0.281988204386 ^ 2 / (2 * 0.560504921783 * 112.827301660546) := by gcongr
    _ ≤ (0.162046597434 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700751075) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377015057)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281988204386) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12730 12730 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504921783 : ℝ) ≤ plow 12730 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.827301660546 : ℝ) ≤ √(12730 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12730 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12730 Θ 1.22 ≤ 0.011753365369 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.827301660546 := by gcongr <;> linarith
      _ ≤ (0.011753365369 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12730 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12730 12730 0.011 ≤ 0.008472125154 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12730 12730 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12730 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12730 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12730 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12730 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162046597434 + 0.011753365369 + (0.008472125154 : ℝ) *
        (1 + 2 * (0.281988204386 + 0.011753365369) / (0.560504921783 * 112.827301660546))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12730]

end BstLean.Part269.N12730

/-! The original eight local profiles supply actual 12730 moment certificates. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12730 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052700751075 ∧
    0 ≤ bN 12730 BstLean.Part154.csC (groupTheta g) ∧ bN 12730 BstLean.Part154.csC (groupTheta g) ≤ 0.001377015057 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12730 12730 0.011
      (momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12730 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12730 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12730 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229566441527 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12730 0.011
      (momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12730 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12730
/-! The actual computed-centre upper energy formula at 12730. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12730

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12730)
open BstLean.Part268 (cell12730)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085403250255
  | 2 => 0.086344411926
  | 3 => 0.087283483387
  | 4 => 0.088221829625
  | 5 => 0.089161103401
  | 6 => 0.090103288213
  | 7 => 0.091050745350
  | 8 => 0.092006265071
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12730 12730 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12730 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12730

/-! Actual upper energy certificates on all 43 source endpoints at 12730. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12730)
open BstLean.Part268 (cell12730)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12730 (gMinus 12730) (1 - (cell12730 i).lower) ≤ 1 ∧
    energyUpper 12730 (gMinus 12730) (BstLean.Part211.gPlus 12730)
      (finiteEnergy 12730 12730 0.011) (1 - (cell12730 i).lower) ≤
      (cell12730 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨10,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨11,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨12,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨13,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨14,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨15,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨16,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨17,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨18,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨19,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨20,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨21,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨22,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨23,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨24,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨25,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨26,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨27,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨28,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨29,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨30,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨31,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨32,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨33,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨34,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨35,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨36,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨37,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨38,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨39,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨40,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨41,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨42,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨43,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨44,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨45,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨46,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨47,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨48,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨49,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨50,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨51,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12730) (by norm_num)
        (q := 1 - (cell12730 ⟨52,by decide⟩).lower)
        (by norm_num [cell12730]) (by norm_num [cell12730])
      exact ⟨E.1,E.2.trans (by norm_num [cell12730])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12730

/-! Source-cell containment and simple scalar guards at 12730. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12730)
open BstLean.Part268 (cell12730)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12730 ⟨10,by decide⟩).lower ∧ (cell12730 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12730 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12730 ⟨11,by decide⟩).lower ∧ (cell12730 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12730 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12730 ⟨12,by decide⟩).lower ∧ (cell12730 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12730 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12730 ⟨13,by decide⟩).lower ∧ (cell12730 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12730 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12730 ⟨14,by decide⟩).lower ∧ (cell12730 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12730 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12730 ⟨15,by decide⟩).lower ∧ (cell12730 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12730 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12730 ⟨16,by decide⟩).lower ∧ (cell12730 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12730 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12730 ⟨17,by decide⟩).lower ∧ (cell12730 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12730 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12730 ⟨18,by decide⟩).lower ∧ (cell12730 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12730 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12730 ⟨19,by decide⟩).lower ∧ (cell12730 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12730 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12730 ⟨20,by decide⟩).lower ∧ (cell12730 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12730 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12730 ⟨21,by decide⟩).lower ∧ (cell12730 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12730 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12730 ⟨22,by decide⟩).lower ∧ (cell12730 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12730 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12730 ⟨23,by decide⟩).lower ∧ (cell12730 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12730 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12730 ⟨24,by decide⟩).lower ∧ (cell12730 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12730 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12730 ⟨25,by decide⟩).lower ∧ (cell12730 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12730 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12730 ⟨26,by decide⟩).lower ∧ (cell12730 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12730 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12730 ⟨27,by decide⟩).lower ∧ (cell12730 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12730 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12730 ⟨28,by decide⟩).lower ∧ (cell12730 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12730 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12730 ⟨29,by decide⟩).lower ∧ (cell12730 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12730 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12730 ⟨30,by decide⟩).lower ∧ (cell12730 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12730 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12730 ⟨31,by decide⟩).lower ∧ (cell12730 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12730 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12730 ⟨32,by decide⟩).lower ∧ (cell12730 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12730 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12730 ⟨33,by decide⟩).lower ∧ (cell12730 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12730 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12730 ⟨34,by decide⟩).lower ∧ (cell12730 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12730 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12730 ⟨35,by decide⟩).lower ∧ (cell12730 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12730 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12730 ⟨36,by decide⟩).lower ∧ (cell12730 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12730 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12730 ⟨37,by decide⟩).lower ∧ (cell12730 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12730 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12730 ⟨38,by decide⟩).lower ∧ (cell12730 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12730 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12730 ⟨39,by decide⟩).lower ∧ (cell12730 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12730 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12730 ⟨40,by decide⟩).lower ∧ (cell12730 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12730 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12730 ⟨41,by decide⟩).lower ∧ (cell12730 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12730 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12730 ⟨42,by decide⟩).lower ∧ (cell12730 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12730 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12730 ⟨43,by decide⟩).lower ∧ (cell12730 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12730 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12730 ⟨44,by decide⟩).lower ∧ (cell12730 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12730 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12730 ⟨45,by decide⟩).lower ∧ (cell12730 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12730 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12730 ⟨46,by decide⟩).lower ∧ (cell12730 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12730 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12730 ⟨47,by decide⟩).lower ∧ (cell12730 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12730 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12730 ⟨48,by decide⟩).lower ∧ (cell12730 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12730 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12730 ⟨49,by decide⟩).lower ∧ (cell12730 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12730 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12730 ⟨50,by decide⟩).lower ∧ (cell12730 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12730 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12730 ⟨51,by decide⟩).lower ∧ (cell12730 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12730 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12730 ⟨52,by decide⟩).lower ∧ (cell12730 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12730 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12730 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12730 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12730,cell12730,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12730 i).lower ∧
    (cell12730 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12730 i).upper ≤ (0.532 : ℝ) ∧
    (cell12730 i).centre ≤ (0.1 : ℝ) ∧ (cell12730 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12730 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12730 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12730

/-! The local source numeric instances at 12730 have no network premises. -/
namespace BstLean.Part269.N12730
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12730)
open BstLean.Part268 (cell12730)

noncomputable def sourceNumerics12730 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12730 (cell12730 i)
      scalarRow12730.M scalarRow12730.H scalarRow12730.xi := by
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
    energy_allowance := scalarRow12730.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12730]
    centre_nonneg := (scalarRow12730.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12730])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12730
/-! Actual 12731 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12731 ≤ (1.035765213456 : ℝ) := by
  have hr : (112.831733125038 : ℝ) ≤ √(12731 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.831733125038 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12731 12731 (11 / 1000) ≤
    (0.008471792409 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12731) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.831733125038 : ℝ) ≤ √(12731 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12731)
  have hdiv : K / √(12731 : ℝ) ≤ K / 112.831733125038 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.831733125038 ≤ (0.008471792409 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12731.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12731 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12731 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12731 := gPlus_lower 12731
end BstLean.Part269.N12731

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12731
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035765213455 : ℝ) ≤ wn 12731 := by
  have hn : √(12731 : ℝ) ≤ 112.831733125039 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12731 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.831733125039 ≤ 2 / √(12731 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251256863 : ℝ) ≤ rhoBar 12731 BstLean.Part154.csC ∧
    rhoBar 12731 BstLean.Part154.csC ≤ 0.000251257252 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035765213455 : ℝ) / (1.295212 * 12731) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035765213456 : ℝ) / (1.29521 * 12731) := by gcongr
      _ ≤ (0.000251257252 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12731 BstLean.Part154.csC) ≤ 0.001005092139 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12731 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) ≤ 0.000191911962 ∧
    cc1 (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) ≤ 0.000122114860 ∧
    cc2 (rhoBar 12731 BstLean.Part154.csC) ≤ 0.000070888617 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12731 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12731 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12731 BstLean.Part154.csC * nuR (rhoBar 12731 BstLean.Part154.csC)) ≤ 0.000502530287 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251257252 : ℝ) * 0.001005092139 := by gcongr
      _ ≤ (0.000502530287 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12731 BstLean.Part154.csC) * nuR (rhoBar 12731 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005092139 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12731 BstLean.Part154.csC) * rhoBar 12731 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251257252 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251257252 / 2 + 0.399 * 0.001005092139 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191911962 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502530287 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122114860 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251257252 / 1.414213562 := by gcongr
      _ ≤ (0.000070888617 : ℝ) := by norm_num

end BstLean.Part269.N12731

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12731
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) ≤ 1.59052E-7 := by
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12731 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12731 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12731 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191911962 : ℝ) ^ 2 + 0.000122114860 ^ 2 + 3 * 0.000070888617 ^ 2 +
        2 * 0.797885 * 0.000191911962 * 0.000122114860 + 2 * 0.000191911962 * 0.000070888617 +
        4 * 0.797885 * 0.000122114860 * 0.000070888617 := by gcongr
    _ ≤ (1.59052E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12731 BstLean.Part154.csC Θ ≤ 0.002622663147 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12731 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12731 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12731 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035765213456 * 1.59052E-7 / (0.000251256863 : ℝ) := by gcongr
    _ ≤ 0.002622663147 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12731 BstLean.Part154.csC Θ ≤ 0.002909862910 + 0.000662704823 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12731 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12731 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035765213456 : ℝ) * ((2 * Θ * 0.000251257252 +
        (6863 / 10000) * 0.000251257252 * 12731 * 0.001005092139) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002909862910 + 0.000662704823 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12731 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12731 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12731 0.011 Θ ∧ gammaRatio 12731 0.011 Θ ≤ 0.000086375746 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12731 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035765213456 : ℝ) * 0.525 / ((1 - 0.011) * 12731) := by gcongr
      _ ≤ (0.000086375746 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12731 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12731 0.011 Θ) :=
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
    badAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12731 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12731 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12731 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12731 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12731 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12731 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12731 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12731 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12731 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12731 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035765213456 : ℝ) * 12731 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003468947141 + 0.003285367970 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12731

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12731
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12731 BstLean.Part154.csC) (piBar (rhoBar 12731 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12731 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12731 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12731 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12731 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12731 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12731 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12731 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12731 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12731 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12731 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052419681697 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12731) ≤ 0.010584235020 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12731 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035765213456)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010584235020 + 2 * 0.737676 / 12731) := by gcongr
    _ ≤ (0.052419681697 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12731 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12731

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12731
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504966789 : ℝ) ≤ plow 12731 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12731) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700365326)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376898153) : eMP 12731 0.011 xi bn ≤ 0.001185416150 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12731 : ℝ) * (1 - 0.011))) ≤ 0.000586133393 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376898153 / (12731 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586133393 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586133393 : ℝ) + 3.141593 * 0.052700365326 / (12731 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185416150 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700365326)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376898153) : PiBarMP 12731 12 0.011 xi bn ≤ 0.161052373814 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12731 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037106578299 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.209442561666 : ℝ) ≤ √((12731 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.831733125038 : ℝ) ≤ √(12731 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12731) ≤ 0.123479520140 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037106578299 + 0.052700365326 * 1.772454 / (2 * (112.209442561666 : ℝ))) * (1 + 0.001185416150) +
        8 / (12731 * 112.831733125038) + 0.123479520140 := by gcongr
    _ ≤ (0.161052373814 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700365326)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376898153) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281985283054) :
    parallelOracle 12731 0.011 xi bn cd ≤ 0.162040076795 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12731 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12731 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504966789 : ℝ) ≤ plow 12731 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.831733125038 : ℝ) ≤ √(12731 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281985283054 : ℝ) / (2 * 0.560504966789 * 112.831733125038)) * 0.161052373814 +
        0.281985283054 ^ 2 / (2 * 0.560504966789 * 112.831733125038) := by gcongr
    _ ≤ (0.162040076795 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052700365326) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376898153)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281985283054) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12731 12731 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504966789 : ℝ) ≤ plow 12731 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.831733125038 : ℝ) ≤ √(12731 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12731 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12731 Θ 1.22 ≤ 0.011752903756 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.831733125038 := by gcongr <;> linarith
      _ ≤ (0.011752903756 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12731 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12731 12731 0.011 ≤ 0.008471792409 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12731 12731 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12731 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12731 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12731 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12731 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162040076795 + 0.011752903756 + (0.008471792409 : ℝ) *
        (1 + 2 * (0.281985283054 + 0.011752903756) / (0.560504966789 * 112.831733125038))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12731]

end BstLean.Part269.N12731

/-! The original eight local profiles supply actual 12731 moment certificates. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12731 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052700365326 ∧
    0 ≤ bN 12731 BstLean.Part154.csC (groupTheta g) ∧ bN 12731 BstLean.Part154.csC (groupTheta g) ≤ 0.001376898153 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12731 12731 0.011
      (momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12731 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12731 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12731 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229565601357 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12731 0.011
      (momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12731 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12731
/-! The actual computed-centre upper energy formula at 12731. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12731

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12731)
open BstLean.Part268 (cell12731)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085400366517
  | 2 => 0.086341475940
  | 3 => 0.087280487649
  | 4 => 0.088218764895
  | 5 => 0.089157958394
  | 6 => 0.090100049252
  | 7 => 0.091047395979
  | 8 => 0.092002785626
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12731 12731 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12731 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12731

/-! Actual upper energy certificates on all 43 source endpoints at 12731. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12731)
open BstLean.Part268 (cell12731)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12731 (gMinus 12731) (1 - (cell12731 i).lower) ≤ 1 ∧
    energyUpper 12731 (gMinus 12731) (BstLean.Part211.gPlus 12731)
      (finiteEnergy 12731 12731 0.011) (1 - (cell12731 i).lower) ≤
      (cell12731 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨10,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨11,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨12,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨13,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨14,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨15,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨16,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨17,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨18,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨19,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨20,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨21,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨22,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨23,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨24,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨25,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨26,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨27,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨28,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨29,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨30,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨31,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨32,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨33,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨34,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨35,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨36,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨37,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨38,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨39,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨40,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨41,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨42,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨43,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨44,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨45,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨46,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨47,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨48,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨49,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨50,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨51,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12731) (by norm_num)
        (q := 1 - (cell12731 ⟨52,by decide⟩).lower)
        (by norm_num [cell12731]) (by norm_num [cell12731])
      exact ⟨E.1,E.2.trans (by norm_num [cell12731])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12731

/-! Source-cell containment and simple scalar guards at 12731. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12731)
open BstLean.Part268 (cell12731)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12731 ⟨10,by decide⟩).lower ∧ (cell12731 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12731 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12731 ⟨11,by decide⟩).lower ∧ (cell12731 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12731 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12731 ⟨12,by decide⟩).lower ∧ (cell12731 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12731 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12731 ⟨13,by decide⟩).lower ∧ (cell12731 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12731 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12731 ⟨14,by decide⟩).lower ∧ (cell12731 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12731 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12731 ⟨15,by decide⟩).lower ∧ (cell12731 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12731 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12731 ⟨16,by decide⟩).lower ∧ (cell12731 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12731 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12731 ⟨17,by decide⟩).lower ∧ (cell12731 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12731 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12731 ⟨18,by decide⟩).lower ∧ (cell12731 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12731 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12731 ⟨19,by decide⟩).lower ∧ (cell12731 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12731 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12731 ⟨20,by decide⟩).lower ∧ (cell12731 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12731 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12731 ⟨21,by decide⟩).lower ∧ (cell12731 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12731 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12731 ⟨22,by decide⟩).lower ∧ (cell12731 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12731 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12731 ⟨23,by decide⟩).lower ∧ (cell12731 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12731 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12731 ⟨24,by decide⟩).lower ∧ (cell12731 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12731 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12731 ⟨25,by decide⟩).lower ∧ (cell12731 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12731 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12731 ⟨26,by decide⟩).lower ∧ (cell12731 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12731 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12731 ⟨27,by decide⟩).lower ∧ (cell12731 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12731 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12731 ⟨28,by decide⟩).lower ∧ (cell12731 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12731 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12731 ⟨29,by decide⟩).lower ∧ (cell12731 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12731 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12731 ⟨30,by decide⟩).lower ∧ (cell12731 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12731 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12731 ⟨31,by decide⟩).lower ∧ (cell12731 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12731 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12731 ⟨32,by decide⟩).lower ∧ (cell12731 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12731 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12731 ⟨33,by decide⟩).lower ∧ (cell12731 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12731 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12731 ⟨34,by decide⟩).lower ∧ (cell12731 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12731 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12731 ⟨35,by decide⟩).lower ∧ (cell12731 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12731 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12731 ⟨36,by decide⟩).lower ∧ (cell12731 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12731 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12731 ⟨37,by decide⟩).lower ∧ (cell12731 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12731 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12731 ⟨38,by decide⟩).lower ∧ (cell12731 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12731 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12731 ⟨39,by decide⟩).lower ∧ (cell12731 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12731 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12731 ⟨40,by decide⟩).lower ∧ (cell12731 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12731 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12731 ⟨41,by decide⟩).lower ∧ (cell12731 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12731 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12731 ⟨42,by decide⟩).lower ∧ (cell12731 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12731 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12731 ⟨43,by decide⟩).lower ∧ (cell12731 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12731 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12731 ⟨44,by decide⟩).lower ∧ (cell12731 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12731 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12731 ⟨45,by decide⟩).lower ∧ (cell12731 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12731 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12731 ⟨46,by decide⟩).lower ∧ (cell12731 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12731 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12731 ⟨47,by decide⟩).lower ∧ (cell12731 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12731 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12731 ⟨48,by decide⟩).lower ∧ (cell12731 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12731 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12731 ⟨49,by decide⟩).lower ∧ (cell12731 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12731 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12731 ⟨50,by decide⟩).lower ∧ (cell12731 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12731 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12731 ⟨51,by decide⟩).lower ∧ (cell12731 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12731 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12731 ⟨52,by decide⟩).lower ∧ (cell12731 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12731 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12731 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12731 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12731,cell12731,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12731 i).lower ∧
    (cell12731 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12731 i).upper ≤ (0.532 : ℝ) ∧
    (cell12731 i).centre ≤ (0.1 : ℝ) ∧ (cell12731 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12731 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12731 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12731

/-! The local source numeric instances at 12731 have no network premises. -/
namespace BstLean.Part269.N12731
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12731)
open BstLean.Part268 (cell12731)

noncomputable def sourceNumerics12731 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12731 (cell12731 i)
      scalarRow12731.M scalarRow12731.H scalarRow12731.xi := by
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
    energy_allowance := scalarRow12731.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12731]
    centre_nonneg := (scalarRow12731.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12731])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12731
/-! Actual 12732 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12732 ≤ (1.035763796550 : ℝ) := by
  have hr : (112.836164415492 : ℝ) ≤ √(12732 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.836164415492 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12732 12732 (11 / 1000) ≤
    (0.008471459703 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12732) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.836164415492 : ℝ) ≤ √(12732 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12732)
  have hdiv : K / √(12732 : ℝ) ≤ K / 112.836164415492 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.836164415492 ≤ (0.008471459703 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12732.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12732 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12732 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12732 := gPlus_lower 12732
end BstLean.Part269.N12732

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12732
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035763796549 : ℝ) ≤ wn 12732 := by
  have hn : √(12732 : ℝ) ≤ 112.836164415493 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12732 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.836164415493 ≤ 2 / √(12732 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251236785 : ℝ) ≤ rhoBar 12732 BstLean.Part154.csC ∧
    rhoBar 12732 BstLean.Part154.csC ≤ 0.000251237174 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035763796549 : ℝ) / (1.295212 * 12732) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035763796550 : ℝ) / (1.29521 * 12732) := by gcongr
      _ ≤ (0.000251237174 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12732 BstLean.Part154.csC) ≤ 0.001005011817 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12732 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) ≤ 0.000191896626 ∧
    cc1 (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) ≤ 0.000122105102 ∧
    cc2 (rhoBar 12732 BstLean.Part154.csC) ≤ 0.000070882953 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12732 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12732 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12732 BstLean.Part154.csC * nuR (rhoBar 12732 BstLean.Part154.csC)) ≤ 0.000502490129 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251237174 : ℝ) * 0.001005011817 := by gcongr
      _ ≤ (0.000502490129 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12732 BstLean.Part154.csC) * nuR (rhoBar 12732 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005011817 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12732 BstLean.Part154.csC) * rhoBar 12732 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251237174 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251237174 / 2 + 0.399 * 0.001005011817 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191896626 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502490129 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122105102 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251237174 / 1.414213562 := by gcongr
      _ ≤ (0.000070882953 : ℝ) := by norm_num

end BstLean.Part269.N12732

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12732
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) ≤ 1.59027E-7 := by
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12732 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12732 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12732 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191896626 : ℝ) ^ 2 + 0.000122105102 ^ 2 + 3 * 0.000070882953 ^ 2 +
        2 * 0.797885 * 0.000191896626 * 0.000122105102 + 2 * 0.000191896626 * 0.000070882953 +
        4 * 0.797885 * 0.000122105102 * 0.000070882953 := by gcongr
    _ ≤ (1.59027E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12732 BstLean.Part154.csC Θ ≤ 0.002622456888 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12732 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12732 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12732 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035763796550 * 1.59027E-7 / (0.000251236785 : ℝ) := by gcongr
    _ ≤ 0.002622456888 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12732 BstLean.Part154.csC Θ ≤ 0.002909622408 + 0.000662650960 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12732 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12732 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035763796550 : ℝ) * ((2 * Θ * 0.000251237174 +
        (6863 / 10000) * 0.000251237174 * 12732 * 0.001005011817) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002909622408 + 0.000662650960 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12732 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12732 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12732 0.011 Θ ∧ gammaRatio 12732 0.011 Θ ≤ 0.000086368844 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12732 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035763796550 : ℝ) * 0.525 / ((1 - 0.011) * 12732) := by gcongr
      _ ≤ (0.000086368844 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12732 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12732 0.011 Θ) :=
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
    badAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12732 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12732 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12732 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12732 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12732 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12732 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12732 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12732 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12732 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12732 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035763796550 : ℝ) * 12732 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003468706639 + 0.003285107848 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12732

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12732
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12732 BstLean.Part154.csC) (piBar (rhoBar 12732 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12732 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12732 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12732 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12732 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12732 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12732 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12732 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12732 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12732 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12732 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052417600782 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12732) ≤ 0.010583819357 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12732 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035763796550)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010583819357 + 2 * 0.737676 / 12732) := by gcongr
    _ ≤ (0.052417600782 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12732 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12732

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12732
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505011789 : ℝ) ≤ plow 12732 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12732) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699988260)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376789867) : eMP 12732 0.011 xi bn ≤ 0.001185322891 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12732 : ℝ) * (1 - 0.011))) ≤ 0.000586087327 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376789867 / (12732 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586087327 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586087327 : ℝ) + 3.141593 * 0.052699988260 / (12732 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185322891 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699988260)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376789867) : PiBarMP 12732 12 0.011 xi bn ≤ 0.161046040156 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12732 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037105119149 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.213849412628 : ℝ) ≤ √((12732 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.836164415492 : ℝ) ≤ √(12732 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12732) ≤ 0.123474670864 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037105119149 + 0.052699988260 * 1.772454 / (2 * (112.213849412628 : ℝ))) * (1 + 0.001185322891) +
        8 / (12732 * 112.836164415492) + 0.123474670864 := by gcongr
    _ ≤ (0.161046040156 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699988260)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376789867) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281982380877) :
    parallelOracle 12732 0.011 xi bn cd ≤ 0.162033673515 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12732 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12732 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505011789 : ℝ) ≤ plow 12732 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.836164415492 : ℝ) ≤ √(12732 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281982380877 : ℝ) / (2 * 0.560505011789 * 112.836164415492)) * 0.161046040156 +
        0.281982380877 ^ 2 / (2 * 0.560505011789 * 112.836164415492) := by gcongr
    _ ≤ (0.162033673515 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699988260) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376789867)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281982380877) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12732 12732 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505011789 : ℝ) ≤ plow 12732 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.836164415492 : ℝ) ≤ √(12732 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12732 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12732 Θ 1.22 ≤ 0.011752442197 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.836164415492 := by gcongr <;> linarith
      _ ≤ (0.011752442197 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12732 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12732 12732 0.011 ≤ 0.008471459703 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12732 12732 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12732 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12732 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12732 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12732 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162033673515 + 0.011752442197 + (0.008471459703 : ℝ) *
        (1 + 2 * (0.281982380877 + 0.011752442197) / (0.560505011789 * 112.836164415492))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12732]

end BstLean.Part269.N12732

/-! The original eight local profiles supply actual 12732 moment certificates. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12732 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052699988260 ∧
    0 ≤ bN 12732 BstLean.Part154.csC (groupTheta g) ∧ bN 12732 BstLean.Part154.csC (groupTheta g) ≤ 0.001376789867 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12732 12732 0.011
      (momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12732 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12732 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12732 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229564780095 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12732 0.011
      (momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12732 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12732
/-! The actual computed-centre upper energy formula at 12732. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12732

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12732)
open BstLean.Part268 (cell12732)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085397483829
  | 2 => 0.086338541047
  | 3 => 0.087277493057
  | 4 => 0.088215701376
  | 5 => 0.089154814677
  | 6 => 0.090096811678
  | 7 => 0.091044048113
  | 8 => 0.091999307826
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12732 12732 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12732 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12732

/-! Actual upper energy certificates on all 43 source endpoints at 12732. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12732)
open BstLean.Part268 (cell12732)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12732 (gMinus 12732) (1 - (cell12732 i).lower) ≤ 1 ∧
    energyUpper 12732 (gMinus 12732) (BstLean.Part211.gPlus 12732)
      (finiteEnergy 12732 12732 0.011) (1 - (cell12732 i).lower) ≤
      (cell12732 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨10,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨11,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨12,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨13,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨14,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨15,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨16,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨17,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨18,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨19,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨20,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨21,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨22,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨23,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨24,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨25,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨26,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨27,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨28,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨29,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨30,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨31,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨32,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨33,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨34,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨35,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨36,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨37,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨38,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨39,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨40,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨41,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨42,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨43,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨44,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨45,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨46,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨47,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨48,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨49,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨50,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨51,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12732) (by norm_num)
        (q := 1 - (cell12732 ⟨52,by decide⟩).lower)
        (by norm_num [cell12732]) (by norm_num [cell12732])
      exact ⟨E.1,E.2.trans (by norm_num [cell12732])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12732

/-! Source-cell containment and simple scalar guards at 12732. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12732)
open BstLean.Part268 (cell12732)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12732 ⟨10,by decide⟩).lower ∧ (cell12732 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12732 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12732 ⟨11,by decide⟩).lower ∧ (cell12732 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12732 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12732 ⟨12,by decide⟩).lower ∧ (cell12732 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12732 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12732 ⟨13,by decide⟩).lower ∧ (cell12732 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12732 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12732 ⟨14,by decide⟩).lower ∧ (cell12732 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12732 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12732 ⟨15,by decide⟩).lower ∧ (cell12732 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12732 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12732 ⟨16,by decide⟩).lower ∧ (cell12732 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12732 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12732 ⟨17,by decide⟩).lower ∧ (cell12732 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12732 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12732 ⟨18,by decide⟩).lower ∧ (cell12732 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12732 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12732 ⟨19,by decide⟩).lower ∧ (cell12732 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12732 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12732 ⟨20,by decide⟩).lower ∧ (cell12732 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12732 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12732 ⟨21,by decide⟩).lower ∧ (cell12732 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12732 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12732 ⟨22,by decide⟩).lower ∧ (cell12732 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12732 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12732 ⟨23,by decide⟩).lower ∧ (cell12732 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12732 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12732 ⟨24,by decide⟩).lower ∧ (cell12732 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12732 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12732 ⟨25,by decide⟩).lower ∧ (cell12732 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12732 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12732 ⟨26,by decide⟩).lower ∧ (cell12732 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12732 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12732 ⟨27,by decide⟩).lower ∧ (cell12732 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12732 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12732 ⟨28,by decide⟩).lower ∧ (cell12732 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12732 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12732 ⟨29,by decide⟩).lower ∧ (cell12732 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12732 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12732 ⟨30,by decide⟩).lower ∧ (cell12732 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12732 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12732 ⟨31,by decide⟩).lower ∧ (cell12732 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12732 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12732 ⟨32,by decide⟩).lower ∧ (cell12732 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12732 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12732 ⟨33,by decide⟩).lower ∧ (cell12732 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12732 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12732 ⟨34,by decide⟩).lower ∧ (cell12732 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12732 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12732 ⟨35,by decide⟩).lower ∧ (cell12732 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12732 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12732 ⟨36,by decide⟩).lower ∧ (cell12732 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12732 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12732 ⟨37,by decide⟩).lower ∧ (cell12732 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12732 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12732 ⟨38,by decide⟩).lower ∧ (cell12732 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12732 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12732 ⟨39,by decide⟩).lower ∧ (cell12732 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12732 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12732 ⟨40,by decide⟩).lower ∧ (cell12732 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12732 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12732 ⟨41,by decide⟩).lower ∧ (cell12732 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12732 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12732 ⟨42,by decide⟩).lower ∧ (cell12732 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12732 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12732 ⟨43,by decide⟩).lower ∧ (cell12732 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12732 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12732 ⟨44,by decide⟩).lower ∧ (cell12732 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12732 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12732 ⟨45,by decide⟩).lower ∧ (cell12732 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12732 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12732 ⟨46,by decide⟩).lower ∧ (cell12732 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12732 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12732 ⟨47,by decide⟩).lower ∧ (cell12732 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12732 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12732 ⟨48,by decide⟩).lower ∧ (cell12732 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12732 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12732 ⟨49,by decide⟩).lower ∧ (cell12732 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12732 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12732 ⟨50,by decide⟩).lower ∧ (cell12732 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12732 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12732 ⟨51,by decide⟩).lower ∧ (cell12732 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12732 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12732 ⟨52,by decide⟩).lower ∧ (cell12732 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12732 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12732 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12732 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12732,cell12732,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12732 i).lower ∧
    (cell12732 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12732 i).upper ≤ (0.532 : ℝ) ∧
    (cell12732 i).centre ≤ (0.1 : ℝ) ∧ (cell12732 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12732 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12732 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12732

/-! The local source numeric instances at 12732 have no network premises. -/
namespace BstLean.Part269.N12732
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12732)
open BstLean.Part268 (cell12732)

noncomputable def sourceNumerics12732 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12732 (cell12732 i)
      scalarRow12732.M scalarRow12732.H scalarRow12732.xi := by
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
    energy_allowance := scalarRow12732.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12732]
    centre_nonneg := (scalarRow12732.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12732])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12732
/-! Actual 12733 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12733 ≤ (1.035762379811 : ℝ) := by
  have hr : (112.840595531927 : ℝ) ≤ √(12733 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.840595531927 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12733 12733 (11 / 1000) ≤
    (0.008471127036 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12733) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.840595531927 : ℝ) ≤ √(12733 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12733)
  have hdiv : K / √(12733 : ℝ) ≤ K / 112.840595531927 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.840595531927 ≤ (0.008471127036 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12733.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12733 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12733 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12733 := gPlus_lower 12733
end BstLean.Part269.N12733

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12733
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035762379810 : ℝ) ≤ wn 12733 := by
  have hn : √(12733 : ℝ) ≤ 112.840595531928 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12733 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.840595531928 ≤ 2 / √(12733 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251216711 : ℝ) ≤ rhoBar 12733 BstLean.Part154.csC ∧
    rhoBar 12733 BstLean.Part154.csC ≤ 0.000251217100 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035762379810 : ℝ) / (1.295212 * 12733) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035762379811 : ℝ) / (1.29521 * 12733) := by gcongr
      _ ≤ (0.000251217100 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12733 BstLean.Part154.csC) ≤ 0.001004931511 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12733 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) ≤ 0.000191881292 ∧
    cc1 (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) ≤ 0.000122095345 ∧
    cc2 (rhoBar 12733 BstLean.Part154.csC) ≤ 0.000070877289 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12733 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12733 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12733 BstLean.Part154.csC * nuR (rhoBar 12733 BstLean.Part154.csC)) ≤ 0.000502449978 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251217100 : ℝ) * 0.001004931511 := by gcongr
      _ ≤ (0.000502449978 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12733 BstLean.Part154.csC) * nuR (rhoBar 12733 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004931511 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12733 BstLean.Part154.csC) * rhoBar 12733 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251217100 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251217100 / 2 + 0.399 * 0.001004931511 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191881292 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502449978 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122095345 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251217100 / 1.414213562 := by gcongr
      _ ≤ (0.000070877289 : ℝ) := by norm_num

end BstLean.Part269.N12733

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12733
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) ≤ 1.59001E-7 := by
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12733 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12733 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12733 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191881292 : ℝ) ^ 2 + 0.000122095345 ^ 2 + 3 * 0.000070877289 ^ 2 +
        2 * 0.797885 * 0.000191881292 * 0.000122095345 + 2 * 0.000191881292 * 0.000070877289 +
        4 * 0.797885 * 0.000122095345 * 0.000070877289 := by gcongr
    _ ≤ (1.59001E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12733 BstLean.Part154.csC Θ ≤ 0.002622234063 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12733 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12733 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12733 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035762379811 * 1.59001E-7 / (0.000251216711 : ℝ) := by gcongr
    _ ≤ 0.002622234063 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12733 BstLean.Part154.csC Θ ≤ 0.002909381963 + 0.000662597108 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12733 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12733 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035762379811 : ℝ) * ((2 * Θ * 0.000251217100 +
        (6863 / 10000) * 0.000251217100 * 12733 * 0.001004931511) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002909381963 + 0.000662597108 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12733 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12733 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12733 0.011 Θ ∧ gammaRatio 12733 0.011 Θ ≤ 0.000086361943 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12733 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035762379811 : ℝ) * 0.525 / ((1 - 0.011) * 12733) := by gcongr
      _ ≤ (0.000086361943 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12733 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12733 0.011 Θ) :=
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
    badAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12733 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12733 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12733 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12733 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12733 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12733 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12733 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12733 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12733 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12733 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035762379811 : ℝ) * 12733 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003468466194 + 0.003284831171 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12733

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12733
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12733 BstLean.Part154.csC) (piBar (rhoBar 12733 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12733 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12733 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12733 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12733 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12733 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12733 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12733 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12733 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12733 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12733 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052415520114 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12733) ≤ 0.010583403743 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12733 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035762379811)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010583403743 + 2 * 0.737676 / 12733) := by gcongr
    _ ≤ (0.052415520114 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12733 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12733

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12733
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505056781 : ℝ) ≤ plow 12733 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12733) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699602559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376672884) : eMP 12733 0.011 xi bn ≤ 0.001185225934 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12733 : ℝ) * (1 - 0.011))) ≤ 0.000586039413 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376672884 / (12733 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586039413 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586039413 : ℝ) + 3.141593 * 0.052699602559 / (12733 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185225934 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699602559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376672884) : PiBarMP 12733 12 0.011 xi bn ≤ 0.161039589470 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12733 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037103542742 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.218256090531 : ℝ) ≤ √((12733 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.840595531927 : ℝ) ≤ √(12733 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12733) ≤ 0.123469822160 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037103542742 + 0.052699602559 * 1.772454 / (2 * (112.218256090531 : ℝ))) * (1 + 0.001185225934) +
        8 / (12733 * 112.840595531927) + 0.123469822160 := by gcongr
    _ ≤ (0.161039589470 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699602559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376672884) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281979460138) :
    parallelOracle 12733 0.011 xi bn cd ≤ 0.162027152846 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12733 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12733 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505056781 : ℝ) ≤ plow 12733 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.840595531927 : ℝ) ≤ √(12733 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281979460138 : ℝ) / (2 * 0.560505056781 * 112.840595531927)) * 0.161039589470 +
        0.281979460138 ^ 2 / (2 * 0.560505056781 * 112.840595531927) := by gcongr
    _ ≤ (0.162027152846 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699602559) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376672884)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281979460138) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12733 12733 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505056781 : ℝ) ≤ plow 12733 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.840595531927 : ℝ) ≤ √(12733 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12733 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12733 Θ 1.22 ≤ 0.011751980693 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.840595531927 := by gcongr <;> linarith
      _ ≤ (0.011751980693 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12733 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12733 12733 0.011 ≤ 0.008471127036 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12733 12733 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12733 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12733 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12733 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12733 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162027152846 + 0.011751980693 + (0.008471127036 : ℝ) *
        (1 + 2 * (0.281979460138 + 0.011751980693) / (0.560505056781 * 112.840595531927))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12733]

end BstLean.Part269.N12733

/-! The original eight local profiles supply actual 12733 moment certificates. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12733 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052699602559 ∧
    0 ≤ bN 12733 BstLean.Part154.csC (groupTheta g) ∧ bN 12733 BstLean.Part154.csC (groupTheta g) ≤ 0.001376672884 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12733 12733 0.011
      (momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12733 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12733 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12733 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229563940024 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12733 0.011
      (momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12733 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12733
/-! The actual computed-centre upper energy formula at 12733. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12733

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12733)
open BstLean.Part268 (cell12733)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085394602191
  | 2 => 0.086335607246
  | 3 => 0.087274499610
  | 4 => 0.088212639067
  | 5 => 0.089151672250
  | 6 => 0.090093575490
  | 7 => 0.091040701749
  | 8 => 0.091995831668
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12733 12733 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12733 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12733

/-! Actual upper energy certificates on all 43 source endpoints at 12733. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12733)
open BstLean.Part268 (cell12733)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12733 (gMinus 12733) (1 - (cell12733 i).lower) ≤ 1 ∧
    energyUpper 12733 (gMinus 12733) (BstLean.Part211.gPlus 12733)
      (finiteEnergy 12733 12733 0.011) (1 - (cell12733 i).lower) ≤
      (cell12733 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨10,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨11,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨12,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨13,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨14,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨15,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨16,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨17,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨18,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨19,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨20,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨21,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨22,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨23,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨24,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨25,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨26,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨27,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨28,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨29,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨30,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨31,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨32,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨33,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨34,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨35,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨36,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨37,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨38,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨39,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨40,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨41,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨42,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨43,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨44,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨45,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨46,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨47,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨48,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨49,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨50,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨51,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12733) (by norm_num)
        (q := 1 - (cell12733 ⟨52,by decide⟩).lower)
        (by norm_num [cell12733]) (by norm_num [cell12733])
      exact ⟨E.1,E.2.trans (by norm_num [cell12733])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12733

/-! Source-cell containment and simple scalar guards at 12733. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12733)
open BstLean.Part268 (cell12733)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12733 ⟨10,by decide⟩).lower ∧ (cell12733 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12733 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12733 ⟨11,by decide⟩).lower ∧ (cell12733 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12733 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12733 ⟨12,by decide⟩).lower ∧ (cell12733 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12733 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12733 ⟨13,by decide⟩).lower ∧ (cell12733 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12733 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12733 ⟨14,by decide⟩).lower ∧ (cell12733 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12733 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12733 ⟨15,by decide⟩).lower ∧ (cell12733 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12733 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12733 ⟨16,by decide⟩).lower ∧ (cell12733 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12733 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12733 ⟨17,by decide⟩).lower ∧ (cell12733 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12733 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12733 ⟨18,by decide⟩).lower ∧ (cell12733 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12733 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12733 ⟨19,by decide⟩).lower ∧ (cell12733 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12733 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12733 ⟨20,by decide⟩).lower ∧ (cell12733 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12733 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12733 ⟨21,by decide⟩).lower ∧ (cell12733 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12733 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12733 ⟨22,by decide⟩).lower ∧ (cell12733 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12733 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12733 ⟨23,by decide⟩).lower ∧ (cell12733 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12733 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12733 ⟨24,by decide⟩).lower ∧ (cell12733 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12733 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12733 ⟨25,by decide⟩).lower ∧ (cell12733 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12733 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12733 ⟨26,by decide⟩).lower ∧ (cell12733 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12733 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12733 ⟨27,by decide⟩).lower ∧ (cell12733 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12733 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12733 ⟨28,by decide⟩).lower ∧ (cell12733 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12733 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12733 ⟨29,by decide⟩).lower ∧ (cell12733 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12733 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12733 ⟨30,by decide⟩).lower ∧ (cell12733 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12733 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12733 ⟨31,by decide⟩).lower ∧ (cell12733 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12733 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12733 ⟨32,by decide⟩).lower ∧ (cell12733 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12733 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12733 ⟨33,by decide⟩).lower ∧ (cell12733 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12733 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12733 ⟨34,by decide⟩).lower ∧ (cell12733 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12733 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12733 ⟨35,by decide⟩).lower ∧ (cell12733 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12733 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12733 ⟨36,by decide⟩).lower ∧ (cell12733 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12733 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12733 ⟨37,by decide⟩).lower ∧ (cell12733 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12733 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12733 ⟨38,by decide⟩).lower ∧ (cell12733 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12733 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12733 ⟨39,by decide⟩).lower ∧ (cell12733 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12733 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12733 ⟨40,by decide⟩).lower ∧ (cell12733 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12733 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12733 ⟨41,by decide⟩).lower ∧ (cell12733 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12733 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12733 ⟨42,by decide⟩).lower ∧ (cell12733 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12733 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12733 ⟨43,by decide⟩).lower ∧ (cell12733 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12733 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12733 ⟨44,by decide⟩).lower ∧ (cell12733 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12733 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12733 ⟨45,by decide⟩).lower ∧ (cell12733 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12733 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12733 ⟨46,by decide⟩).lower ∧ (cell12733 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12733 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12733 ⟨47,by decide⟩).lower ∧ (cell12733 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12733 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12733 ⟨48,by decide⟩).lower ∧ (cell12733 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12733 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12733 ⟨49,by decide⟩).lower ∧ (cell12733 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12733 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12733 ⟨50,by decide⟩).lower ∧ (cell12733 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12733 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12733 ⟨51,by decide⟩).lower ∧ (cell12733 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12733 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12733 ⟨52,by decide⟩).lower ∧ (cell12733 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12733 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12733 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12733 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12733,cell12733,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12733 i).lower ∧
    (cell12733 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12733 i).upper ≤ (0.532 : ℝ) ∧
    (cell12733 i).centre ≤ (0.1 : ℝ) ∧ (cell12733 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12733 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12733 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12733

/-! The local source numeric instances at 12733 have no network premises. -/
namespace BstLean.Part269.N12733
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12733)
open BstLean.Part268 (cell12733)

noncomputable def sourceNumerics12733 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12733 (cell12733 i)
      scalarRow12733.M scalarRow12733.H scalarRow12733.xi := by
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
    energy_allowance := scalarRow12733.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12733]
    centre_nonneg := (scalarRow12733.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12733])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12733
/-! Actual 12734 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12734 ≤ (1.035760963240 : ℝ) := by
  have hr : (112.845026474364 : ℝ) ≤ √(12734 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.845026474364 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12734 12734 (11 / 1000) ≤
    (0.008470794409 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12734) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.845026474364 : ℝ) ≤ √(12734 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12734)
  have hdiv : K / √(12734 : ℝ) ≤ K / 112.845026474364 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.845026474364 ≤ (0.008470794409 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12734.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12734 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12734 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12734 := gPlus_lower 12734
end BstLean.Part269.N12734

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12734
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035760963239 : ℝ) ≤ wn 12734 := by
  have hn : √(12734 : ℝ) ≤ 112.845026474365 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12734 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.845026474365 ≤ 2 / √(12734 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251196639 : ℝ) ≤ rhoBar 12734 BstLean.Part154.csC ∧
    rhoBar 12734 BstLean.Part154.csC ≤ 0.000251197028 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035760963239 : ℝ) / (1.295212 * 12734) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035760963240 : ℝ) / (1.29521 * 12734) := by gcongr
      _ ≤ (0.000251197028 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12734 BstLean.Part154.csC) ≤ 0.001004851212 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12734 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) ≤ 0.000191865960 ∧
    cc1 (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) ≤ 0.000122085589 ∧
    cc2 (rhoBar 12734 BstLean.Part154.csC) ≤ 0.000070871626 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12734 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12734 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12734 BstLean.Part154.csC * nuR (rhoBar 12734 BstLean.Part154.csC)) ≤ 0.000502409831 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251197028 : ℝ) * 0.001004851212 := by gcongr
      _ ≤ (0.000502409831 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12734 BstLean.Part154.csC) * nuR (rhoBar 12734 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004851212 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12734 BstLean.Part154.csC) * rhoBar 12734 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251197028 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251197028 / 2 + 0.399 * 0.001004851212 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191865960 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502409831 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122085589 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251197028 / 1.414213562 := by gcongr
      _ ≤ (0.000070871626 : ℝ) := by norm_num

end BstLean.Part269.N12734

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12734
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) ≤ 1.58976E-7 := by
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12734 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12734 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12734 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191865960 : ℝ) ^ 2 + 0.000122085589 ^ 2 + 3 * 0.000070871626 ^ 2 +
        2 * 0.797885 * 0.000191865960 * 0.000122085589 + 2 * 0.000191865960 * 0.000070871626 +
        4 * 0.797885 * 0.000122085589 * 0.000070871626 := by gcongr
    _ ≤ (1.58976E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12734 BstLean.Part154.csC Θ ≤ 0.002622027676 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12734 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12734 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12734 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035760963240 * 1.58976E-7 / (0.000251196639 : ℝ) := by gcongr
    _ ≤ 0.002622027676 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12734 BstLean.Part154.csC Θ ≤ 0.002909141527 + 0.000662543261 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12734 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12734 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035760963240 : ℝ) * ((2 * Θ * 0.000251197028 +
        (6863 / 10000) * 0.000251197028 * 12734 * 0.001004851212) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002909141527 + 0.000662543261 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12734 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12734 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12734 0.011 Θ ∧ gammaRatio 12734 0.011 Θ ≤ 0.000086355043 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12734 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035760963240 : ℝ) * 0.525 / ((1 - 0.011) * 12734) := by gcongr
      _ ≤ (0.000086355043 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12734 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12734 0.011 Θ) :=
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
    badAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12734 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12734 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12734 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12734 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12734 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12734 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12734 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12734 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12734 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12734 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035760963240 : ℝ) * 12734 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003468225758 + 0.003284570937 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12734

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12734
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12734 BstLean.Part154.csC) (piBar (rhoBar 12734 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12734 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12734 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12734 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12734 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12734 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12734 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12734 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12734 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12734 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12734 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052413439693 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12734) ≤ 0.010582988178 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12734 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035760963240)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010582988178 + 2 * 0.737676 / 12734) := by gcongr
    _ ≤ (0.052413439693 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12734 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12734

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12734
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505101766 : ℝ) ≤ plow 12734 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12734) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699225500)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376564530) : eMP 12734 0.011 xi bn ≤ 0.001185132660 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12734 : ℝ) * (1 - 0.011))) ≤ 0.000585993339 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376564530 / (12734 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585993339 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585993339 : ℝ) + 3.141593 * 0.052699225500 / (12734 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185132660 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699225500)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376564530) : PiBarMP 12734 12 0.011 xi bn ≤ 0.161033255925 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12734 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037102082557 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.222662595395 : ℝ) ≤ √((12734 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.845026474364 : ℝ) ≤ √(12734 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12734) ≤ 0.123464974028 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037102082557 + 0.052699225500 * 1.772454 / (2 * (112.222662595395 : ℝ))) * (1 + 0.001185132660) +
        8 / (12734 * 112.845026474364) + 0.123464974028 := by gcongr
    _ ≤ (0.161033255925 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699225500)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376564530) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281976558465) :
    parallelOracle 12734 0.011 xi bn cd ≤ 0.162020749697 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12734 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12734 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505101766 : ℝ) ≤ plow 12734 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.845026474364 : ℝ) ≤ √(12734 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281976558465 : ℝ) / (2 * 0.560505101766 * 112.845026474364)) * 0.161033255925 +
        0.281976558465 ^ 2 / (2 * 0.560505101766 * 112.845026474364) := by gcongr
    _ ≤ (0.162020749697 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052699225500) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376564530)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281976558465) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12734 12734 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505101766 : ℝ) ≤ plow 12734 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.845026474364 : ℝ) ≤ √(12734 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12734 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12734 Θ 1.22 ≤ 0.011751519243 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.845026474364 := by gcongr <;> linarith
      _ ≤ (0.011751519243 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12734 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12734 12734 0.011 ≤ 0.008470794409 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12734 12734 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12734 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12734 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12734 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12734 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162020749697 + 0.011751519243 + (0.008470794409 : ℝ) *
        (1 + 2 * (0.281976558465 + 0.011751519243) / (0.560505101766 * 112.845026474364))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12734]

end BstLean.Part269.N12734

/-! The original eight local profiles supply actual 12734 moment certificates. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12734 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052699225500 ∧
    0 ≤ bN 12734 BstLean.Part154.csC (groupTheta g) ∧ bN 12734 BstLean.Part154.csC (groupTheta g) ≤ 0.001376564530 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12734 12734 0.011
      (momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12734 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12734 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12734 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229563118772 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12734 0.011
      (momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12734 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12734
/-! The actual computed-centre upper energy formula at 12734. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12734

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12734)
open BstLean.Part268 (cell12734)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085391721601
  | 2 => 0.086332674536
  | 3 => 0.087271507307
  | 4 => 0.088209577966
  | 5 => 0.089148531110
  | 6 => 0.090090340686
  | 7 => 0.091037356885
  | 8 => 0.091992357151
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12734 12734 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12734 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12734

/-! Actual upper energy certificates on all 43 source endpoints at 12734. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12734)
open BstLean.Part268 (cell12734)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12734 (gMinus 12734) (1 - (cell12734 i).lower) ≤ 1 ∧
    energyUpper 12734 (gMinus 12734) (BstLean.Part211.gPlus 12734)
      (finiteEnergy 12734 12734 0.011) (1 - (cell12734 i).lower) ≤
      (cell12734 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨10,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨11,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨12,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨13,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨14,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨15,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨16,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨17,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨18,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨19,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨20,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨21,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨22,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨23,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨24,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨25,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨26,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨27,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨28,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨29,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨30,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨31,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨32,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨33,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨34,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨35,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨36,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨37,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨38,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨39,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨40,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨41,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨42,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨43,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨44,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨45,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨46,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨47,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨48,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨49,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨50,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨51,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12734) (by norm_num)
        (q := 1 - (cell12734 ⟨52,by decide⟩).lower)
        (by norm_num [cell12734]) (by norm_num [cell12734])
      exact ⟨E.1,E.2.trans (by norm_num [cell12734])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12734

/-! Source-cell containment and simple scalar guards at 12734. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12734)
open BstLean.Part268 (cell12734)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12734 ⟨10,by decide⟩).lower ∧ (cell12734 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12734 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12734 ⟨11,by decide⟩).lower ∧ (cell12734 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12734 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12734 ⟨12,by decide⟩).lower ∧ (cell12734 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12734 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12734 ⟨13,by decide⟩).lower ∧ (cell12734 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12734 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12734 ⟨14,by decide⟩).lower ∧ (cell12734 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12734 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12734 ⟨15,by decide⟩).lower ∧ (cell12734 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12734 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12734 ⟨16,by decide⟩).lower ∧ (cell12734 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12734 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12734 ⟨17,by decide⟩).lower ∧ (cell12734 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12734 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12734 ⟨18,by decide⟩).lower ∧ (cell12734 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12734 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12734 ⟨19,by decide⟩).lower ∧ (cell12734 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12734 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12734 ⟨20,by decide⟩).lower ∧ (cell12734 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12734 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12734 ⟨21,by decide⟩).lower ∧ (cell12734 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12734 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12734 ⟨22,by decide⟩).lower ∧ (cell12734 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12734 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12734 ⟨23,by decide⟩).lower ∧ (cell12734 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12734 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12734 ⟨24,by decide⟩).lower ∧ (cell12734 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12734 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12734 ⟨25,by decide⟩).lower ∧ (cell12734 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12734 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12734 ⟨26,by decide⟩).lower ∧ (cell12734 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12734 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12734 ⟨27,by decide⟩).lower ∧ (cell12734 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12734 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12734 ⟨28,by decide⟩).lower ∧ (cell12734 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12734 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12734 ⟨29,by decide⟩).lower ∧ (cell12734 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12734 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12734 ⟨30,by decide⟩).lower ∧ (cell12734 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12734 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12734 ⟨31,by decide⟩).lower ∧ (cell12734 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12734 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12734 ⟨32,by decide⟩).lower ∧ (cell12734 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12734 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12734 ⟨33,by decide⟩).lower ∧ (cell12734 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12734 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12734 ⟨34,by decide⟩).lower ∧ (cell12734 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12734 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12734 ⟨35,by decide⟩).lower ∧ (cell12734 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12734 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12734 ⟨36,by decide⟩).lower ∧ (cell12734 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12734 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12734 ⟨37,by decide⟩).lower ∧ (cell12734 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12734 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12734 ⟨38,by decide⟩).lower ∧ (cell12734 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12734 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12734 ⟨39,by decide⟩).lower ∧ (cell12734 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12734 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12734 ⟨40,by decide⟩).lower ∧ (cell12734 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12734 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12734 ⟨41,by decide⟩).lower ∧ (cell12734 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12734 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12734 ⟨42,by decide⟩).lower ∧ (cell12734 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12734 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12734 ⟨43,by decide⟩).lower ∧ (cell12734 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12734 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12734 ⟨44,by decide⟩).lower ∧ (cell12734 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12734 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12734 ⟨45,by decide⟩).lower ∧ (cell12734 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12734 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12734 ⟨46,by decide⟩).lower ∧ (cell12734 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12734 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12734 ⟨47,by decide⟩).lower ∧ (cell12734 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12734 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12734 ⟨48,by decide⟩).lower ∧ (cell12734 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12734 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12734 ⟨49,by decide⟩).lower ∧ (cell12734 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12734 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12734 ⟨50,by decide⟩).lower ∧ (cell12734 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12734 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12734 ⟨51,by decide⟩).lower ∧ (cell12734 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12734 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12734 ⟨52,by decide⟩).lower ∧ (cell12734 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12734 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12734 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12734 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12734,cell12734,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12734 i).lower ∧
    (cell12734 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12734 i).upper ≤ (0.532 : ℝ) ∧
    (cell12734 i).centre ≤ (0.1 : ℝ) ∧ (cell12734 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12734 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12734 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12734

/-! The local source numeric instances at 12734 have no network premises. -/
namespace BstLean.Part269.N12734
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12734)
open BstLean.Part268 (cell12734)

noncomputable def sourceNumerics12734 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12734 (cell12734 i)
      scalarRow12734.M scalarRow12734.H scalarRow12734.xi := by
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
    energy_allowance := scalarRow12734.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12734]
    centre_nonneg := (scalarRow12734.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12734])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12734
/-! Actual 12735 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12735 ≤ (1.035759546838 : ℝ) := by
  have hr : (112.849457242824 : ℝ) ≤ √(12735 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.849457242824 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12735 12735 (11 / 1000) ≤
    (0.008470461820 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12735) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.849457242824 : ℝ) ≤ √(12735 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12735)
  have hdiv : K / √(12735 : ℝ) ≤ K / 112.849457242824 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.849457242824 ≤ (0.008470461820 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12735.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12735 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12735 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12735 := gPlus_lower 12735
end BstLean.Part269.N12735

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12735
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035759546837 : ℝ) ≤ wn 12735 := by
  have hn : √(12735 : ℝ) ≤ 112.849457242825 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12735 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.849457242825 ≤ 2 / √(12735 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251176571 : ℝ) ≤ rhoBar 12735 BstLean.Part154.csC ∧
    rhoBar 12735 BstLean.Part154.csC ≤ 0.000251176960 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035759546837 : ℝ) / (1.295212 * 12735) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035759546838 : ℝ) / (1.29521 * 12735) := by gcongr
      _ ≤ (0.000251176960 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12735 BstLean.Part154.csC) ≤ 0.001004770930 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12735 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) ≤ 0.000191850632 ∧
    cc1 (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) ≤ 0.000122075836 ∧
    cc2 (rhoBar 12735 BstLean.Part154.csC) ≤ 0.000070865964 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12735 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12735 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12735 BstLean.Part154.csC * nuR (rhoBar 12735 BstLean.Part154.csC)) ≤ 0.000502369693 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251176960 : ℝ) * 0.001004770930 := by gcongr
      _ ≤ (0.000502369693 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12735 BstLean.Part154.csC) * nuR (rhoBar 12735 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004770930 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12735 BstLean.Part154.csC) * rhoBar 12735 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251176960 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251176960 / 2 + 0.399 * 0.001004770930 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191850632 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502369693 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122075836 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251176960 / 1.414213562 := by gcongr
      _ ≤ (0.000070865964 : ℝ) := by norm_num

end BstLean.Part269.N12735

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12735
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) ≤ 1.58951E-7 := by
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12735 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12735 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12735 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191850632 : ℝ) ^ 2 + 0.000122075836 ^ 2 + 3 * 0.000070865964 ^ 2 +
        2 * 0.797885 * 0.000191850632 * 0.000122075836 + 2 * 0.000191850632 * 0.000070865964 +
        4 * 0.797885 * 0.000122075836 * 0.000070865964 := by gcongr
    _ ≤ (1.58951E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12735 BstLean.Part154.csC Θ ≤ 0.002621821217 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12735 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12735 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12735 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035759546838 * 1.58951E-7 / (0.000251176571 : ℝ) := by gcongr
    _ ≤ 0.002621821217 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12735 BstLean.Part154.csC Θ ≤ 0.002908901152 + 0.000662489424 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12735 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12735 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035759546838 : ℝ) * ((2 * Θ * 0.000251176960 +
        (6863 / 10000) * 0.000251176960 * 12735 * 0.001004770930) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002908901152 + 0.000662489424 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12735 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12735 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12735 0.011 Θ ∧ gammaRatio 12735 0.011 Θ ≤ 0.000086348144 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12735 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035759546838 : ℝ) * 0.525 / ((1 - 0.011) * 12735) := by gcongr
      _ ≤ (0.000086348144 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12735 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12735 0.011 Θ) :=
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
    badAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12735 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12735 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12735 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12735 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12735 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12735 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12735 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12735 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12735 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12735 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035759546838 : ℝ) * 12735 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003467985383 + 0.003284310641 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12735

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12735
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12735 BstLean.Part154.csC) (piBar (rhoBar 12735 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12735 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12735 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12735 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12735 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12735 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12735 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12735 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12735 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12735 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12735 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052411359519 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12735) ≤ 0.010582572662 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12735 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035759546838)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010582572662 + 2 * 0.737676 / 12735) := by gcongr
    _ ≤ (0.052411359519 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12735 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12735

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12735
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505146745 : ℝ) ≤ plow 12735 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12735) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698848470)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376456139) : eMP 12735 0.011 xi bn ≤ 0.001185039378 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12735 : ℝ) * (1 - 0.011))) ≤ 0.000585947261 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376456139 / (12735 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585947261 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585947261 : ℝ) + 3.141593 * 0.052698848470 / (12735 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001185039378 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698848470)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376456139) : PiBarMP 12735 12 0.011 xi bn ≤ 0.161026922394 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12735 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037100621815 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.227068927242 : ℝ) ≤ √((12735 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.849457242824 : ℝ) ≤ √(12735 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12735) ≤ 0.123460126466 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037100621815 + 0.052698848470 * 1.772454 / (2 * (112.227068927242 : ℝ))) * (1 + 0.001185039378) +
        8 / (12735 * 112.849457242824) + 0.123460126466 := by gcongr
    _ ≤ (0.161026922394 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698848470)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376456139) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281973657099) :
    parallelOracle 12735 0.011 xi bn cd ≤ 0.162014346570 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12735 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12735 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505146745 : ℝ) ≤ plow 12735 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.849457242824 : ℝ) ≤ √(12735 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281973657099 : ℝ) / (2 * 0.560505146745 * 112.849457242824)) * 0.161026922394 +
        0.281973657099 ^ 2 / (2 * 0.560505146745 * 112.849457242824) := by gcongr
    _ ≤ (0.162014346570 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698848470) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376456139)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281973657099) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12735 12735 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505146745 : ℝ) ≤ plow 12735 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.849457242824 : ℝ) ≤ √(12735 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12735 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12735 Θ 1.22 ≤ 0.011751057847 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.849457242824 := by gcongr <;> linarith
      _ ≤ (0.011751057847 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12735 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12735 12735 0.011 ≤ 0.008470461820 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12735 12735 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12735 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12735 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12735 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12735 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162014346570 + 0.011751057847 + (0.008470461820 : ℝ) *
        (1 + 2 * (0.281973657099 + 0.011751057847) / (0.560505146745 * 112.849457242824))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12735]

end BstLean.Part269.N12735

/-! The original eight local profiles supply actual 12735 moment certificates. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12735 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052698848470 ∧
    0 ≤ bN 12735 BstLean.Part154.csC (groupTheta g) ∧ bN 12735 BstLean.Part154.csC (groupTheta g) ≤ 0.001376456139 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12735 12735 0.011
      (momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12735 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12735 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12735 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229562297580 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12735 0.011
      (momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12735 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12735
/-! The actual computed-centre upper energy formula at 12735. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12735

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12735)
open BstLean.Part268 (cell12735)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085388842058
  | 2 => 0.086329742916
  | 3 => 0.087268516146
  | 4 => 0.088206518073
  | 5 => 0.089145391256
  | 6 => 0.090087107264
  | 7 => 0.091034013519
  | 8 => 0.091988884272
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12735 12735 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12735 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12735

/-! Actual upper energy certificates on all 43 source endpoints at 12735. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12735)
open BstLean.Part268 (cell12735)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12735 (gMinus 12735) (1 - (cell12735 i).lower) ≤ 1 ∧
    energyUpper 12735 (gMinus 12735) (BstLean.Part211.gPlus 12735)
      (finiteEnergy 12735 12735 0.011) (1 - (cell12735 i).lower) ≤
      (cell12735 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨10,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨11,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨12,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨13,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨14,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨15,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨16,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨17,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨18,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨19,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨20,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨21,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨22,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨23,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨24,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨25,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨26,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨27,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨28,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨29,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨30,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨31,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨32,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨33,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨34,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨35,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨36,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨37,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨38,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨39,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨40,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨41,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨42,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨43,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨44,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨45,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨46,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨47,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨48,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨49,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨50,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨51,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12735) (by norm_num)
        (q := 1 - (cell12735 ⟨52,by decide⟩).lower)
        (by norm_num [cell12735]) (by norm_num [cell12735])
      exact ⟨E.1,E.2.trans (by norm_num [cell12735])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12735

/-! Source-cell containment and simple scalar guards at 12735. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12735)
open BstLean.Part268 (cell12735)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12735 ⟨10,by decide⟩).lower ∧ (cell12735 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12735 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12735 ⟨11,by decide⟩).lower ∧ (cell12735 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12735 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12735 ⟨12,by decide⟩).lower ∧ (cell12735 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12735 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12735 ⟨13,by decide⟩).lower ∧ (cell12735 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12735 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12735 ⟨14,by decide⟩).lower ∧ (cell12735 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12735 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12735 ⟨15,by decide⟩).lower ∧ (cell12735 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12735 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12735 ⟨16,by decide⟩).lower ∧ (cell12735 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12735 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12735 ⟨17,by decide⟩).lower ∧ (cell12735 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12735 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12735 ⟨18,by decide⟩).lower ∧ (cell12735 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12735 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12735 ⟨19,by decide⟩).lower ∧ (cell12735 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12735 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12735 ⟨20,by decide⟩).lower ∧ (cell12735 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12735 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12735 ⟨21,by decide⟩).lower ∧ (cell12735 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12735 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12735 ⟨22,by decide⟩).lower ∧ (cell12735 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12735 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12735 ⟨23,by decide⟩).lower ∧ (cell12735 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12735 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12735 ⟨24,by decide⟩).lower ∧ (cell12735 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12735 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12735 ⟨25,by decide⟩).lower ∧ (cell12735 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12735 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12735 ⟨26,by decide⟩).lower ∧ (cell12735 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12735 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12735 ⟨27,by decide⟩).lower ∧ (cell12735 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12735 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12735 ⟨28,by decide⟩).lower ∧ (cell12735 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12735 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12735 ⟨29,by decide⟩).lower ∧ (cell12735 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12735 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12735 ⟨30,by decide⟩).lower ∧ (cell12735 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12735 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12735 ⟨31,by decide⟩).lower ∧ (cell12735 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12735 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12735 ⟨32,by decide⟩).lower ∧ (cell12735 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12735 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12735 ⟨33,by decide⟩).lower ∧ (cell12735 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12735 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12735 ⟨34,by decide⟩).lower ∧ (cell12735 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12735 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12735 ⟨35,by decide⟩).lower ∧ (cell12735 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12735 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12735 ⟨36,by decide⟩).lower ∧ (cell12735 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12735 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12735 ⟨37,by decide⟩).lower ∧ (cell12735 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12735 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12735 ⟨38,by decide⟩).lower ∧ (cell12735 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12735 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12735 ⟨39,by decide⟩).lower ∧ (cell12735 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12735 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12735 ⟨40,by decide⟩).lower ∧ (cell12735 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12735 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12735 ⟨41,by decide⟩).lower ∧ (cell12735 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12735 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12735 ⟨42,by decide⟩).lower ∧ (cell12735 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12735 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12735 ⟨43,by decide⟩).lower ∧ (cell12735 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12735 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12735 ⟨44,by decide⟩).lower ∧ (cell12735 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12735 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12735 ⟨45,by decide⟩).lower ∧ (cell12735 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12735 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12735 ⟨46,by decide⟩).lower ∧ (cell12735 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12735 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12735 ⟨47,by decide⟩).lower ∧ (cell12735 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12735 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12735 ⟨48,by decide⟩).lower ∧ (cell12735 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12735 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12735 ⟨49,by decide⟩).lower ∧ (cell12735 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12735 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12735 ⟨50,by decide⟩).lower ∧ (cell12735 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12735 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12735 ⟨51,by decide⟩).lower ∧ (cell12735 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12735 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12735 ⟨52,by decide⟩).lower ∧ (cell12735 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12735 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12735 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12735 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12735,cell12735,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12735 i).lower ∧
    (cell12735 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12735 i).upper ≤ (0.532 : ℝ) ∧
    (cell12735 i).centre ≤ (0.1 : ℝ) ∧ (cell12735 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12735 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12735 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12735

/-! The local source numeric instances at 12735 have no network premises. -/
namespace BstLean.Part269.N12735
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12735)
open BstLean.Part268 (cell12735)

noncomputable def sourceNumerics12735 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12735 (cell12735 i)
      scalarRow12735.M scalarRow12735.H scalarRow12735.xi := by
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
    energy_allowance := scalarRow12735.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12735]
    centre_nonneg := (scalarRow12735.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12735])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12735
/-! Actual 12736 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12736 ≤ (1.035758130603 : ℝ) := by
  have hr : (112.853887837327 : ℝ) ≤ √(12736 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.853887837327 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12736 12736 (11 / 1000) ≤
    (0.008470129271 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12736) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.853887837327 : ℝ) ≤ √(12736 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12736)
  have hdiv : K / √(12736 : ℝ) ≤ K / 112.853887837327 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.853887837327 ≤ (0.008470129271 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12736.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12736 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12736 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12736 := gPlus_lower 12736
end BstLean.Part269.N12736

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12736
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035758130602 : ℝ) ≤ wn 12736 := by
  have hn : √(12736 : ℝ) ≤ 112.853887837328 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12736 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.853887837328 ≤ 2 / √(12736 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251156505 : ℝ) ≤ rhoBar 12736 BstLean.Part154.csC ∧
    rhoBar 12736 BstLean.Part154.csC ≤ 0.000251156894 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035758130602 : ℝ) / (1.295212 * 12736) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035758130603 : ℝ) / (1.29521 * 12736) := by gcongr
      _ ≤ (0.000251156894 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12736 BstLean.Part154.csC) ≤ 0.001004690656 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12736 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) ≤ 0.000191835304 ∧
    cc1 (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) ≤ 0.000122066083 ∧
    cc2 (rhoBar 12736 BstLean.Part154.csC) ≤ 0.000070860303 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12736 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12736 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12736 BstLean.Part154.csC * nuR (rhoBar 12736 BstLean.Part154.csC)) ≤ 0.000502329558 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251156894 : ℝ) * 0.001004690656 := by gcongr
      _ ≤ (0.000502329558 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12736 BstLean.Part154.csC) * nuR (rhoBar 12736 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004690656 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12736 BstLean.Part154.csC) * rhoBar 12736 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251156894 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251156894 / 2 + 0.399 * 0.001004690656 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191835304 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502329558 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122066083 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251156894 / 1.414213562 := by gcongr
      _ ≤ (0.000070860303 : ℝ) := by norm_num

end BstLean.Part269.N12736

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12736
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) ≤ 1.58925E-7 := by
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12736 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12736 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12736 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191835304 : ℝ) ^ 2 + 0.000122066083 ^ 2 + 3 * 0.000070860303 ^ 2 +
        2 * 0.797885 * 0.000191835304 * 0.000122066083 + 2 * 0.000191835304 * 0.000070860303 +
        4 * 0.797885 * 0.000122066083 * 0.000070860303 := by gcongr
    _ ≤ (1.58925E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12736 BstLean.Part154.csC Θ ≤ 0.002621598209 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12736 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12736 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12736 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035758130603 * 1.58925E-7 / (0.000251156505 : ℝ) := by gcongr
    _ ≤ 0.002621598209 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12736 BstLean.Part154.csC Θ ≤ 0.002908660789 + 0.000662435594 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12736 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12736 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035758130603 : ℝ) * ((2 * Θ * 0.000251156894 +
        (6863 / 10000) * 0.000251156894 * 12736 * 0.001004690656) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002908660789 + 0.000662435594 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12736 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12736 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12736 0.011 Θ ∧ gammaRatio 12736 0.011 Θ ≤ 0.000086341246 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12736 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035758130603 : ℝ) * 0.525 / ((1 - 0.011) * 12736) := by gcongr
      _ ≤ (0.000086341246 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12736 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12736 0.011 Θ) :=
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
    badAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12736 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12736 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12736 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12736 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12736 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12736 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12736 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12736 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12736 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12736 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035758130603 : ℝ) * 12736 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003467745020 + 0.003284033803 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12736

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12736
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12736 BstLean.Part154.csC) (piBar (rhoBar 12736 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12736 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12736 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12736 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12736 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12736 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12736 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12736 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12736 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12736 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12736 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052409279592 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12736) ≤ 0.010582157195 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12736 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035758130603)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010582157195 + 2 * 0.737676 / 12736) := by gcongr
    _ ≤ (0.052409279592 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12736 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12736

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12736
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505191716 : ℝ) ≤ plow 12736 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12736) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698462767)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376339060) : eMP 12736 0.011 xi bn ≤ 0.001184942403 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12736 : ℝ) * (1 - 0.011))) ≤ 0.000585899338 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376339060 / (12736 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585899338 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585899338 : ℝ) + 3.141593 * 0.052698462767 / (12736 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184942403 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698462767)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376339060) : PiBarMP 12736 12 0.011 xi bn ≤ 0.161020471941 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12736 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037099043923 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.231475086091 : ℝ) ≤ √((12736 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.853887837327 : ℝ) ≤ √(12736 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12736) ≤ 0.123455279475 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037099043923 + 0.052698462767 * 1.772454 / (2 * (112.231475086091 : ℝ))) * (1 + 0.001184942403) +
        8 / (12736 * 112.853887837327) + 0.123455279475 := by gcongr
    _ ≤ (0.161020471941 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698462767)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376339060) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281970737087) :
    parallelOracle 12736 0.011 xi bn cd ≤ 0.162007826162 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12736 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12736 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505191716 : ℝ) ≤ plow 12736 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.853887837327 : ℝ) ≤ √(12736 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281970737087 : ℝ) / (2 * 0.560505191716 * 112.853887837327)) * 0.161020471941 +
        0.281970737087 ^ 2 / (2 * 0.560505191716 * 112.853887837327) := by gcongr
    _ ≤ (0.162007826162 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698462767) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376339060)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281970737087) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12736 12736 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505191716 : ℝ) ≤ plow 12736 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.853887837327 : ℝ) ≤ √(12736 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12736 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12736 Θ 1.22 ≤ 0.011750596506 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.853887837327 := by gcongr <;> linarith
      _ ≤ (0.011750596506 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12736 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12736 12736 0.011 ≤ 0.008470129271 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12736 12736 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12736 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12736 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12736 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12736 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162007826162 + 0.011750596506 + (0.008470129271 : ℝ) *
        (1 + 2 * (0.281970737087 + 0.011750596506) / (0.560505191716 * 112.853887837327))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12736]

end BstLean.Part269.N12736

/-! The original eight local profiles supply actual 12736 moment certificates. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12736 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052698462767 ∧
    0 ≤ bN 12736 BstLean.Part154.csC (groupTheta g) ∧ bN 12736 BstLean.Part154.csC (groupTheta g) ≤ 0.001376339060 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12736 12736 0.011
      (momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12736 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12736 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12736 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229561457495 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12736 0.011
      (momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12736 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12736
/-! The actual computed-centre upper energy formula at 12736. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12736

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12736)
open BstLean.Part268 (cell12736)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085385963562
  | 2 => 0.086326812385
  | 3 => 0.087265526127
  | 4 => 0.088203459386
  | 5 => 0.089142252688
  | 6 => 0.090083875223
  | 7 => 0.091030671652
  | 8 => 0.091985413031
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12736 12736 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12736 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12736

/-! Actual upper energy certificates on all 43 source endpoints at 12736. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12736)
open BstLean.Part268 (cell12736)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12736 (gMinus 12736) (1 - (cell12736 i).lower) ≤ 1 ∧
    energyUpper 12736 (gMinus 12736) (BstLean.Part211.gPlus 12736)
      (finiteEnergy 12736 12736 0.011) (1 - (cell12736 i).lower) ≤
      (cell12736 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨10,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨11,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨12,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨13,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨14,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨15,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨16,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨17,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨18,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨19,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨20,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨21,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨22,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨23,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨24,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨25,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨26,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨27,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨28,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨29,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨30,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨31,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨32,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨33,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨34,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨35,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨36,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨37,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨38,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨39,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨40,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨41,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨42,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨43,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨44,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨45,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨46,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨47,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨48,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨49,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨50,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨51,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12736) (by norm_num)
        (q := 1 - (cell12736 ⟨52,by decide⟩).lower)
        (by norm_num [cell12736]) (by norm_num [cell12736])
      exact ⟨E.1,E.2.trans (by norm_num [cell12736])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12736

/-! Source-cell containment and simple scalar guards at 12736. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12736)
open BstLean.Part268 (cell12736)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12736 ⟨10,by decide⟩).lower ∧ (cell12736 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12736 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12736 ⟨11,by decide⟩).lower ∧ (cell12736 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12736 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12736 ⟨12,by decide⟩).lower ∧ (cell12736 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12736 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12736 ⟨13,by decide⟩).lower ∧ (cell12736 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12736 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12736 ⟨14,by decide⟩).lower ∧ (cell12736 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12736 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12736 ⟨15,by decide⟩).lower ∧ (cell12736 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12736 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12736 ⟨16,by decide⟩).lower ∧ (cell12736 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12736 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12736 ⟨17,by decide⟩).lower ∧ (cell12736 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12736 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12736 ⟨18,by decide⟩).lower ∧ (cell12736 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12736 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12736 ⟨19,by decide⟩).lower ∧ (cell12736 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12736 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12736 ⟨20,by decide⟩).lower ∧ (cell12736 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12736 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12736 ⟨21,by decide⟩).lower ∧ (cell12736 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12736 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12736 ⟨22,by decide⟩).lower ∧ (cell12736 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12736 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12736 ⟨23,by decide⟩).lower ∧ (cell12736 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12736 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12736 ⟨24,by decide⟩).lower ∧ (cell12736 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12736 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12736 ⟨25,by decide⟩).lower ∧ (cell12736 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12736 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12736 ⟨26,by decide⟩).lower ∧ (cell12736 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12736 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12736 ⟨27,by decide⟩).lower ∧ (cell12736 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12736 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12736 ⟨28,by decide⟩).lower ∧ (cell12736 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12736 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12736 ⟨29,by decide⟩).lower ∧ (cell12736 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12736 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12736 ⟨30,by decide⟩).lower ∧ (cell12736 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12736 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12736 ⟨31,by decide⟩).lower ∧ (cell12736 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12736 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12736 ⟨32,by decide⟩).lower ∧ (cell12736 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12736 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12736 ⟨33,by decide⟩).lower ∧ (cell12736 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12736 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12736 ⟨34,by decide⟩).lower ∧ (cell12736 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12736 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12736 ⟨35,by decide⟩).lower ∧ (cell12736 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12736 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12736 ⟨36,by decide⟩).lower ∧ (cell12736 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12736 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12736 ⟨37,by decide⟩).lower ∧ (cell12736 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12736 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12736 ⟨38,by decide⟩).lower ∧ (cell12736 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12736 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12736 ⟨39,by decide⟩).lower ∧ (cell12736 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12736 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12736 ⟨40,by decide⟩).lower ∧ (cell12736 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12736 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12736 ⟨41,by decide⟩).lower ∧ (cell12736 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12736 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12736 ⟨42,by decide⟩).lower ∧ (cell12736 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12736 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12736 ⟨43,by decide⟩).lower ∧ (cell12736 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12736 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12736 ⟨44,by decide⟩).lower ∧ (cell12736 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12736 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12736 ⟨45,by decide⟩).lower ∧ (cell12736 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12736 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12736 ⟨46,by decide⟩).lower ∧ (cell12736 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12736 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12736 ⟨47,by decide⟩).lower ∧ (cell12736 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12736 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12736 ⟨48,by decide⟩).lower ∧ (cell12736 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12736 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12736 ⟨49,by decide⟩).lower ∧ (cell12736 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12736 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12736 ⟨50,by decide⟩).lower ∧ (cell12736 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12736 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12736 ⟨51,by decide⟩).lower ∧ (cell12736 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12736 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12736 ⟨52,by decide⟩).lower ∧ (cell12736 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12736 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12736 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12736 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12736,cell12736,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12736 i).lower ∧
    (cell12736 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12736 i).upper ≤ (0.532 : ℝ) ∧
    (cell12736 i).centre ≤ (0.1 : ℝ) ∧ (cell12736 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12736 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12736 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12736

/-! The local source numeric instances at 12736 have no network premises. -/
namespace BstLean.Part269.N12736
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12736)
open BstLean.Part268 (cell12736)

noncomputable def sourceNumerics12736 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12736 (cell12736 i)
      scalarRow12736.M scalarRow12736.H scalarRow12736.xi := by
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
    energy_allowance := scalarRow12736.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12736]
    centre_nonneg := (scalarRow12736.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12736])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12736
/-! Actual 12737 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12737 ≤ (1.035756714535 : ℝ) := by
  have hr : (112.858318257893 : ℝ) ≤ √(12737 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.858318257893 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12737 12737 (11 / 1000) ≤
    (0.008469796761 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12737) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.858318257893 : ℝ) ≤ √(12737 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12737)
  have hdiv : K / √(12737 : ℝ) ≤ K / 112.858318257893 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.858318257893 ≤ (0.008469796761 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12737.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12737 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12737 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12737 := gPlus_lower 12737
end BstLean.Part269.N12737

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12737
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035756714534 : ℝ) ≤ wn 12737 := by
  have hn : √(12737 : ℝ) ≤ 112.858318257894 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12737 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.858318257894 ≤ 2 / √(12737 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251136443 : ℝ) ≤ rhoBar 12737 BstLean.Part154.csC ∧
    rhoBar 12737 BstLean.Part154.csC ≤ 0.000251136832 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035756714534 : ℝ) / (1.295212 * 12737) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035756714535 : ℝ) / (1.29521 * 12737) := by gcongr
      _ ≤ (0.000251136832 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12737 BstLean.Part154.csC) ≤ 0.001004610398 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12737 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) ≤ 0.000191819980 ∧
    cc1 (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) ≤ 0.000122056332 ∧
    cc2 (rhoBar 12737 BstLean.Part154.csC) ≤ 0.000070854643 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12737 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12737 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12737 BstLean.Part154.csC * nuR (rhoBar 12737 BstLean.Part154.csC)) ≤ 0.000502289432 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251136832 : ℝ) * 0.001004610398 := by gcongr
      _ ≤ (0.000502289432 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12737 BstLean.Part154.csC) * nuR (rhoBar 12737 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004610398 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12737 BstLean.Part154.csC) * rhoBar 12737 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251136832 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251136832 / 2 + 0.399 * 0.001004610398 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191819980 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502289432 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122056332 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251136832 / 1.414213562 := by gcongr
      _ ≤ (0.000070854643 : ℝ) := by norm_num

end BstLean.Part269.N12737

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12737
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) ≤ 1.58900E-7 := by
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12737 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12737 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12737 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191819980 : ℝ) ^ 2 + 0.000122056332 ^ 2 + 3 * 0.000070854643 ^ 2 +
        2 * 0.797885 * 0.000191819980 * 0.000122056332 + 2 * 0.000191819980 * 0.000070854643 +
        4 * 0.797885 * 0.000122056332 * 0.000070854643 := by gcongr
    _ ≤ (1.58900E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12737 BstLean.Part154.csC Θ ≤ 0.002621391623 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12737 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12737 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12737 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035756714535 * 1.58900E-7 / (0.000251136443 : ℝ) := by gcongr
    _ ≤ 0.002621391623 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12737 BstLean.Part154.csC Θ ≤ 0.002908420483 + 0.000662381774 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12737 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12737 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035756714535 : ℝ) * ((2 * Θ * 0.000251136832 +
        (6863 / 10000) * 0.000251136832 * 12737 * 0.001004610398) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002908420483 + 0.000662381774 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12737 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12737 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12737 0.011 Θ ∧ gammaRatio 12737 0.011 Θ ≤ 0.000086334349 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12737 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035756714535 : ℝ) * 0.525 / ((1 - 0.011) * 12737) := by gcongr
      _ ≤ (0.000086334349 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12737 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12737 0.011 Θ) :=
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
    badAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12737 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12737 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12737 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12737 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12737 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12737 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12737 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12737 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12737 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12737 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035756714535 : ℝ) * 12737 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003467504714 + 0.003283773397 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12737

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12737
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12737 BstLean.Part154.csC) (piBar (rhoBar 12737 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12737 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12737 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12737 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12737 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12737 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12737 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12737 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12737 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12737 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12737 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052407199907 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12737) ≤ 0.010581741776 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12737 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035756714535)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010581741776 + 2 * 0.737676 / 12737) := by gcongr
    _ ≤ (0.052407199907 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12737 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12737

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12737
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505236680 : ℝ) ≤ plow 12737 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12737) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698085748)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376230603) : eMP 12737 0.011 xi bn ≤ 0.001184849107 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12737 : ℝ) * (1 - 0.011))) ≤ 0.000585853253 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376230603 / (12737 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585853253 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585853253 : ℝ) + 3.141593 * 0.052698085748 / (12737 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184849107 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698085748)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376230603) : PiBarMP 12737 12 0.011 xi bn ≤ 0.161014138547 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12737 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037097582172 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.235881071963 : ℝ) ≤ √((12737 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.858318257893 : ℝ) ≤ √(12737 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12737) ≤ 0.123450433055 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037097582172 + 0.052698085748 * 1.772454 / (2 * (112.235881071963 : ℝ))) * (1 + 0.001184849107) +
        8 / (12737 * 112.858318257893) + 0.123450433055 := by gcongr
    _ ≤ (0.161014138547 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698085748)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376230603) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281967836228) :
    parallelOracle 12737 0.011 xi bn cd ≤ 0.162001423191 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12737 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12737 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505236680 : ℝ) ≤ plow 12737 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.858318257893 : ℝ) ≤ √(12737 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281967836228 : ℝ) / (2 * 0.560505236680 * 112.858318257893)) * 0.161014138547 +
        0.281967836228 ^ 2 / (2 * 0.560505236680 * 112.858318257893) := by gcongr
    _ ≤ (0.162001423191 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052698085748) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376230603)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281967836228) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12737 12737 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505236680 : ℝ) ≤ plow 12737 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.858318257893 : ℝ) ≤ √(12737 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12737 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12737 Θ 1.22 ≤ 0.011750135218 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.858318257893 := by gcongr <;> linarith
      _ ≤ (0.011750135218 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12737 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12737 12737 0.011 ≤ 0.008469796761 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12737 12737 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12737 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12737 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12737 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12737 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162001423191 + 0.011750135218 + (0.008469796761 : ℝ) *
        (1 + 2 * (0.281967836228 + 0.011750135218) / (0.560505236680 * 112.858318257893))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12737]

end BstLean.Part269.N12737

/-! The original eight local profiles supply actual 12737 moment certificates. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12737 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052698085748 ∧
    0 ≤ bN 12737 BstLean.Part154.csC (groupTheta g) ∧ bN 12737 BstLean.Part154.csC (groupTheta g) ≤ 0.001376230603 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12737 12737 0.011
      (momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12737 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12737 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12737 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229560636321 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12737 0.011
      (momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12737 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12737
/-! The actual computed-centre upper energy formula at 12737. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12737

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12737)
open BstLean.Part268 (cell12737)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085383086112
  | 2 => 0.086323882942
  | 3 => 0.087262537248
  | 4 => 0.088200401903
  | 5 => 0.089139115402
  | 6 => 0.090080644561
  | 7 => 0.091027331279
  | 8 => 0.091981943425
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12737 12737 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12737 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12737

/-! Actual upper energy certificates on all 43 source endpoints at 12737. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12737)
open BstLean.Part268 (cell12737)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12737 (gMinus 12737) (1 - (cell12737 i).lower) ≤ 1 ∧
    energyUpper 12737 (gMinus 12737) (BstLean.Part211.gPlus 12737)
      (finiteEnergy 12737 12737 0.011) (1 - (cell12737 i).lower) ≤
      (cell12737 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨10,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨11,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨12,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨13,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨14,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨15,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨16,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨17,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨18,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨19,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨20,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨21,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨22,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨23,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨24,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨25,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨26,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨27,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨28,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨29,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨30,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨31,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨32,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨33,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨34,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨35,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨36,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨37,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨38,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨39,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨40,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨41,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨42,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨43,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨44,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨45,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨46,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨47,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨48,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨49,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨50,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨51,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12737) (by norm_num)
        (q := 1 - (cell12737 ⟨52,by decide⟩).lower)
        (by norm_num [cell12737]) (by norm_num [cell12737])
      exact ⟨E.1,E.2.trans (by norm_num [cell12737])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12737

/-! Source-cell containment and simple scalar guards at 12737. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12737)
open BstLean.Part268 (cell12737)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12737 ⟨10,by decide⟩).lower ∧ (cell12737 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12737 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12737 ⟨11,by decide⟩).lower ∧ (cell12737 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12737 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12737 ⟨12,by decide⟩).lower ∧ (cell12737 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12737 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12737 ⟨13,by decide⟩).lower ∧ (cell12737 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12737 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12737 ⟨14,by decide⟩).lower ∧ (cell12737 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12737 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12737 ⟨15,by decide⟩).lower ∧ (cell12737 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12737 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12737 ⟨16,by decide⟩).lower ∧ (cell12737 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12737 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12737 ⟨17,by decide⟩).lower ∧ (cell12737 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12737 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12737 ⟨18,by decide⟩).lower ∧ (cell12737 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12737 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12737 ⟨19,by decide⟩).lower ∧ (cell12737 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12737 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12737 ⟨20,by decide⟩).lower ∧ (cell12737 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12737 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12737 ⟨21,by decide⟩).lower ∧ (cell12737 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12737 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12737 ⟨22,by decide⟩).lower ∧ (cell12737 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12737 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12737 ⟨23,by decide⟩).lower ∧ (cell12737 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12737 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12737 ⟨24,by decide⟩).lower ∧ (cell12737 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12737 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12737 ⟨25,by decide⟩).lower ∧ (cell12737 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12737 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12737 ⟨26,by decide⟩).lower ∧ (cell12737 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12737 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12737 ⟨27,by decide⟩).lower ∧ (cell12737 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12737 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12737 ⟨28,by decide⟩).lower ∧ (cell12737 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12737 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12737 ⟨29,by decide⟩).lower ∧ (cell12737 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12737 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12737 ⟨30,by decide⟩).lower ∧ (cell12737 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12737 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12737 ⟨31,by decide⟩).lower ∧ (cell12737 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12737 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12737 ⟨32,by decide⟩).lower ∧ (cell12737 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12737 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12737 ⟨33,by decide⟩).lower ∧ (cell12737 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12737 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12737 ⟨34,by decide⟩).lower ∧ (cell12737 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12737 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12737 ⟨35,by decide⟩).lower ∧ (cell12737 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12737 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12737 ⟨36,by decide⟩).lower ∧ (cell12737 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12737 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12737 ⟨37,by decide⟩).lower ∧ (cell12737 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12737 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12737 ⟨38,by decide⟩).lower ∧ (cell12737 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12737 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12737 ⟨39,by decide⟩).lower ∧ (cell12737 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12737 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12737 ⟨40,by decide⟩).lower ∧ (cell12737 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12737 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12737 ⟨41,by decide⟩).lower ∧ (cell12737 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12737 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12737 ⟨42,by decide⟩).lower ∧ (cell12737 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12737 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12737 ⟨43,by decide⟩).lower ∧ (cell12737 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12737 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12737 ⟨44,by decide⟩).lower ∧ (cell12737 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12737 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12737 ⟨45,by decide⟩).lower ∧ (cell12737 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12737 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12737 ⟨46,by decide⟩).lower ∧ (cell12737 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12737 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12737 ⟨47,by decide⟩).lower ∧ (cell12737 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12737 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12737 ⟨48,by decide⟩).lower ∧ (cell12737 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12737 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12737 ⟨49,by decide⟩).lower ∧ (cell12737 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12737 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12737 ⟨50,by decide⟩).lower ∧ (cell12737 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12737 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12737 ⟨51,by decide⟩).lower ∧ (cell12737 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12737 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12737 ⟨52,by decide⟩).lower ∧ (cell12737 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12737 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12737 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12737 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12737,cell12737,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12737 i).lower ∧
    (cell12737 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12737 i).upper ≤ (0.532 : ℝ) ∧
    (cell12737 i).centre ≤ (0.1 : ℝ) ∧ (cell12737 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12737 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12737 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12737

/-! The local source numeric instances at 12737 have no network premises. -/
namespace BstLean.Part269.N12737
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12737)
open BstLean.Part268 (cell12737)

noncomputable def sourceNumerics12737 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12737 (cell12737 i)
      scalarRow12737.M scalarRow12737.H scalarRow12737.xi := by
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
    energy_allowance := scalarRow12737.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12737]
    centre_nonneg := (scalarRow12737.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12737])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12737