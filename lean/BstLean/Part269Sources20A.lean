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
import BstLean.Part269Direction20
import BstLean.Part269Shared20
import BstLean.Part269Finite
import BstLean.Part269Rows20
import BstLean.Part269Source
/-! Actual 12850 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12850 ≤ (1.035597771358 : ℝ) := by
  have hr : (113.357840487546 : ℝ) ≤ √(12850 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.357840487546 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12850 12850 (11 / 1000) ≤
    (0.008432473503 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12850) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.357840487546 : ℝ) ≤ √(12850 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12850)
  have hdiv : K / √(12850 : ℝ) ≤ K / 113.357840487546 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.357840487546 ≤ (0.008432473503 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12850.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12850 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12850 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12850 := gPlus_lower 12850
end BstLean.Part269.N12850

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12850
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035597771357 : ℝ) ≤ wn 12850 := by
  have hn : √(12850 : ℝ) ≤ 113.357840487547 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12850 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.357840487547 ≤ 2 / √(12850 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248889807 : ℝ) ≤ rhoBar 12850 BstLean.Part154.csC ∧
    rhoBar 12850 BstLean.Part154.csC ≤ 0.000248890192 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035597771357 : ℝ) / (1.295212 * 12850) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035597771358 : ℝ) / (1.29521 * 12850) := by gcongr
      _ ≤ (0.000248890192 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12850 BstLean.Part154.csC) ≤ 0.000995622715 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12850 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) ≤ 0.000190103903 ∧
    cc1 (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) ≤ 0.000120964397 ∧
    cc2 (rhoBar 12850 BstLean.Part154.csC) ≤ 0.000070220786 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12850 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12850 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12850 BstLean.Part154.csC * nuR (rhoBar 12850 BstLean.Part154.csC)) ≤ 0.000497795871 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248890192 : ℝ) * 0.000995622715 := by gcongr
      _ ≤ (0.000497795871 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12850 BstLean.Part154.csC) * nuR (rhoBar 12850 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995622715 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12850 BstLean.Part154.csC) * rhoBar 12850 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248890192 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248890192 / 2 + 0.399 * 0.000995622715 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190103903 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497795871 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120964397 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248890192 / 1.414213562 := by gcongr
      _ ≤ (0.000070220786 : ℝ) := by norm_num

end BstLean.Part269.N12850

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12850
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) ≤ 1.56069E-7 := by
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12850 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12850 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12850 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190103903 : ℝ) ^ 2 + 0.000120964397 ^ 2 + 3 * 0.000070220786 ^ 2 +
        2 * 0.797885 * 0.000190103903 * 0.000120964397 + 2 * 0.000190103903 * 0.000070220786 +
        4 * 0.797885 * 0.000120964397 * 0.000070220786 := by gcongr
    _ ≤ (1.56069E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12850 BstLean.Part154.csC Θ ≤ 0.002597530378 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12850 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12850 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12850 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035597771358 * 1.56069E-7 / (0.000248889807 : ℝ) := by gcongr
    _ ≤ 0.002597530378 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12850 BstLean.Part154.csC Θ ≤ 0.002881515911 + 0.000656355449 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12850 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12850 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035597771358 : ℝ) * ((2 * Θ * 0.000248890192 +
        (6863 / 10000) * 0.000248890192 * 12850 * 0.000995622715) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002881515911 + 0.000656355449 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12850 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12850 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12850 0.011 Θ ∧ gammaRatio 12850 0.011 Θ ≤ 0.000085562012 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12850 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035597771358 : ℝ) * 0.525 / ((1 - 0.011) * 12850) := by gcongr
      _ ≤ (0.000085562012 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12850 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12850 0.011 Θ) :=
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
    badAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12850 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12850 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12850 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12850 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12850 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12850 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12850 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12850 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12850 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12850 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035597771358 : ℝ) * 12850 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003364259073 + 0.003253885827 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12850

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12850
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12850 BstLean.Part154.csC) (piBar (rhoBar 12850 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12850 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12850 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12850 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12850 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12850 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12850 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12850 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12850 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12850 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12850 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052173772998 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12850) ≤ 0.010535112313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12850 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035597771358)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010535112313 + 2 * 0.737676 / 12850) := by gcongr
    _ ≤ (0.052173772998 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12850 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12850

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12850
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510272552 : ℝ) ≤ plow 12850 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12850) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052579149133)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363703449) : eMP 12850 0.011 xi bn ≤ 0.001174219523 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12850 : ℝ) * (1 - 0.011))) ≤ 0.000580610948 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363703449 / (12850 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580610948 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580610948 : ℝ) + 3.141593 * 0.052579149133 / (12850 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174219523 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052579149133)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363703449) : PiBarMP 12850 12 0.011 xi bn ≤ 0.160297473198 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12850 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036928355623 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.732648332237 : ℝ) ≤ √((12850 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.357840487546 : ℝ) ≤ √(12850 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12850) ≤ 0.122906436845 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036928355623 + 0.052579149133 * 1.772454 / (2 * (112.732648332237 : ℝ))) * (1 + 0.001174219523) +
        8 / (12850 * 113.357840487546) + 0.122906436845 := by gcongr
    _ ≤ (0.160297473198 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052579149133)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363703449) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281475210266) :
    parallelOracle 12850 0.011 xi bn cd ≤ 0.161276002589 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12850 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12850 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510272552 : ℝ) ≤ plow 12850 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.357840487546 : ℝ) ≤ √(12850 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281475210266 : ℝ) / (2 * 0.560510272552 * 113.357840487546)) * 0.160297473198 +
        0.281475210266 ^ 2 / (2 * 0.560510272552 * 113.357840487546) := by gcongr
    _ ≤ (0.161276002589 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052579149133) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363703449)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281475210266) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12850 12850 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510272552 : ℝ) ≤ plow 12850 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.357840487546 : ℝ) ≤ √(12850 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12850 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12850 Θ 1.22 ≤ 0.011698357117 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.357840487546 := by gcongr <;> linarith
      _ ≤ (0.011698357117 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12850 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12850 12850 0.011 ≤ 0.008432473503 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12850 12850 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12850 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12850 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12850 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12850 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161276002589 + 0.011698357117 + (0.008432473503 : ℝ) *
        (1 + 2 * (0.281475210266 + 0.011698357117) / (0.560510272552 * 113.357840487546))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12850]

end BstLean.Part269.N12850

/-! The original eight local profiles supply actual 12850 moment certificates. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12850 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052579149133 ∧
    0 ≤ bN 12850 BstLean.Part154.csC (groupTheta g) ∧ bN 12850 BstLean.Part154.csC (groupTheta g) ≤ 0.001363703449 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12850 12850 0.011
      (momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12850 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12850 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12850 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229301437268 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12850 0.011
      (momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12850 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12850
/-! The actual computed-centre upper energy formula at 12850. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12850

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12850)
open BstLean.Part268 (cell12850)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085064417526
  | 2 => 0.085999599639
  | 3 => 0.086931859389
  | 4 => 0.087862367351
  | 5 => 0.088792547084
  | 6 => 0.089724113686
  | 7 => 0.090659116157
  | 8 => 0.091599983648
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12850 12850 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12850 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12850

/-! Actual upper energy certificates on all 43 source endpoints at 12850. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12850)
open BstLean.Part268 (cell12850)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12850 (gMinus 12850) (1 - (cell12850 i).lower) ≤ 1 ∧
    energyUpper 12850 (gMinus 12850) (BstLean.Part211.gPlus 12850)
      (finiteEnergy 12850 12850 0.011) (1 - (cell12850 i).lower) ≤
      (cell12850 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨10,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨11,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨12,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨13,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨14,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨15,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨16,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨17,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨18,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨19,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨20,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨21,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨22,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨23,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨24,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨25,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨26,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨27,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨28,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨29,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨30,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨31,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨32,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨33,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨34,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨35,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨36,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨37,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨38,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨39,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨40,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨41,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨42,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨43,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨44,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨45,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨46,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨47,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨48,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨49,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨50,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨51,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12850) (by norm_num)
        (q := 1 - (cell12850 ⟨52,by decide⟩).lower)
        (by norm_num [cell12850]) (by norm_num [cell12850])
      exact ⟨E.1,E.2.trans (by norm_num [cell12850])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12850

/-! Source-cell containment and simple scalar guards at 12850. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12850)
open BstLean.Part268 (cell12850)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12850 ⟨10,by decide⟩).lower ∧ (cell12850 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12850 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12850 ⟨11,by decide⟩).lower ∧ (cell12850 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12850 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12850 ⟨12,by decide⟩).lower ∧ (cell12850 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12850 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12850 ⟨13,by decide⟩).lower ∧ (cell12850 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12850 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12850 ⟨14,by decide⟩).lower ∧ (cell12850 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12850 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12850 ⟨15,by decide⟩).lower ∧ (cell12850 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12850 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12850 ⟨16,by decide⟩).lower ∧ (cell12850 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12850 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12850 ⟨17,by decide⟩).lower ∧ (cell12850 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12850 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12850 ⟨18,by decide⟩).lower ∧ (cell12850 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12850 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12850 ⟨19,by decide⟩).lower ∧ (cell12850 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12850 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12850 ⟨20,by decide⟩).lower ∧ (cell12850 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12850 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12850 ⟨21,by decide⟩).lower ∧ (cell12850 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12850 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12850 ⟨22,by decide⟩).lower ∧ (cell12850 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12850 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12850 ⟨23,by decide⟩).lower ∧ (cell12850 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12850 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12850 ⟨24,by decide⟩).lower ∧ (cell12850 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12850 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12850 ⟨25,by decide⟩).lower ∧ (cell12850 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12850 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12850 ⟨26,by decide⟩).lower ∧ (cell12850 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12850 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12850 ⟨27,by decide⟩).lower ∧ (cell12850 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12850 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12850 ⟨28,by decide⟩).lower ∧ (cell12850 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12850 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12850 ⟨29,by decide⟩).lower ∧ (cell12850 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12850 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12850 ⟨30,by decide⟩).lower ∧ (cell12850 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12850 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12850 ⟨31,by decide⟩).lower ∧ (cell12850 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12850 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12850 ⟨32,by decide⟩).lower ∧ (cell12850 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12850 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12850 ⟨33,by decide⟩).lower ∧ (cell12850 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12850 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12850 ⟨34,by decide⟩).lower ∧ (cell12850 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12850 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12850 ⟨35,by decide⟩).lower ∧ (cell12850 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12850 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12850 ⟨36,by decide⟩).lower ∧ (cell12850 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12850 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12850 ⟨37,by decide⟩).lower ∧ (cell12850 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12850 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12850 ⟨38,by decide⟩).lower ∧ (cell12850 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12850 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12850 ⟨39,by decide⟩).lower ∧ (cell12850 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12850 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12850 ⟨40,by decide⟩).lower ∧ (cell12850 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12850 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12850 ⟨41,by decide⟩).lower ∧ (cell12850 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12850 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12850 ⟨42,by decide⟩).lower ∧ (cell12850 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12850 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12850 ⟨43,by decide⟩).lower ∧ (cell12850 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12850 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12850 ⟨44,by decide⟩).lower ∧ (cell12850 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12850 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12850 ⟨45,by decide⟩).lower ∧ (cell12850 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12850 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12850 ⟨46,by decide⟩).lower ∧ (cell12850 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12850 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12850 ⟨47,by decide⟩).lower ∧ (cell12850 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12850 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12850 ⟨48,by decide⟩).lower ∧ (cell12850 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12850 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12850 ⟨49,by decide⟩).lower ∧ (cell12850 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12850 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12850 ⟨50,by decide⟩).lower ∧ (cell12850 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12850 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12850 ⟨51,by decide⟩).lower ∧ (cell12850 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12850 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12850 ⟨52,by decide⟩).lower ∧ (cell12850 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12850 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12850 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12850 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12850,cell12850,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12850 i).lower ∧
    (cell12850 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12850 i).upper ≤ (0.532 : ℝ) ∧
    (cell12850 i).centre ≤ (0.1 : ℝ) ∧ (cell12850 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12850 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12850 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12850

/-! The local source numeric instances at 12850 have no network premises. -/
namespace BstLean.Part269.N12850
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12850)
open BstLean.Part268 (cell12850)

noncomputable def sourceNumerics12850 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12850 (cell12850 i)
      scalarRow12850.M scalarRow12850.H scalarRow12850.xi := by
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
    energy_allowance := scalarRow12850.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12850]
    centre_nonneg := (scalarRow12850.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12850])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12850
/-! Actual 12851 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12851 ≤ (1.035596374201 : ℝ) := by
  have hr : (113.362251212650 : ℝ) ≤ √(12851 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.362251212650 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12851 12851 (11 / 1000) ≤
    (0.008432145407 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12851) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.362251212650 : ℝ) ≤ √(12851 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12851)
  have hdiv : K / √(12851 : ℝ) ≤ K / 113.362251212650 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.362251212650 ≤ (0.008432145407 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12851.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12851 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12851 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12851 := gPlus_lower 12851
end BstLean.Part269.N12851

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12851
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035596374200 : ℝ) ≤ wn 12851 := by
  have hn : √(12851 : ℝ) ≤ 113.362251212651 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12851 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.362251212651 ≤ 2 / √(12851 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248870104 : ℝ) ≤ rhoBar 12851 BstLean.Part154.csC ∧
    rhoBar 12851 BstLean.Part154.csC ≤ 0.000248870489 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035596374200 : ℝ) / (1.295212 * 12851) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035596374201 : ℝ) / (1.29521 * 12851) := by gcongr
      _ ≤ (0.000248870489 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12851 BstLean.Part154.csC) ≤ 0.000995543893 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12851 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) ≤ 0.000190088853 ∧
    cc1 (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) ≤ 0.000120954821 ∧
    cc2 (rhoBar 12851 BstLean.Part154.csC) ≤ 0.000070215227 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12851 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12851 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12851 BstLean.Part154.csC * nuR (rhoBar 12851 BstLean.Part154.csC)) ≤ 0.000497756463 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248870489 : ℝ) * 0.000995543893 := by gcongr
      _ ≤ (0.000497756463 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12851 BstLean.Part154.csC) * nuR (rhoBar 12851 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995543893 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12851 BstLean.Part154.csC) * rhoBar 12851 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248870489 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248870489 / 2 + 0.399 * 0.000995543893 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190088853 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497756463 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120954821 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248870489 / 1.414213562 := by gcongr
      _ ≤ (0.000070215227 : ℝ) := by norm_num

end BstLean.Part269.N12851

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12851
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) ≤ 1.56045E-7 := by
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12851 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12851 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12851 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190088853 : ℝ) ^ 2 + 0.000120954821 ^ 2 + 3 * 0.000070215227 ^ 2 +
        2 * 0.797885 * 0.000190088853 * 0.000120954821 + 2 * 0.000190088853 * 0.000070215227 +
        4 * 0.797885 * 0.000120954821 * 0.000070215227 := by gcongr
    _ ≤ (1.56045E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12851 BstLean.Part154.csC Θ ≤ 0.002597333045 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12851 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12851 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12851 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035596374201 * 1.56045E-7 / (0.000248870104 : ℝ) := by gcongr
    _ ≤ 0.002597333045 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12851 BstLean.Part154.csC Θ ≤ 0.002881280012 + 0.000656302604 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12851 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12851 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035596374201 : ℝ) * ((2 * Θ * 0.000248870489 +
        (6863 / 10000) * 0.000248870489 * 12851 * 0.000995543893) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002881280012 + 0.000656302604 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12851 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12851 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12851 0.011 Θ ∧ gammaRatio 12851 0.011 Θ ≤ 0.000085555239 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12851 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035596374201 : ℝ) * 0.525 / ((1 - 0.011) * 12851) := by gcongr
      _ ≤ (0.000085555239 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12851 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12851 0.011 Θ) :=
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
    badAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12851 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12851 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12851 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12851 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12851 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12851 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12851 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12851 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12851 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12851 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035596374201 : ℝ) * 12851 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003364023174 + 0.003253635649 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12851

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12851
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12851 BstLean.Part154.csC) (piBar (rhoBar 12851 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12851 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12851 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12851 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12851 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12851 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12851 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12851 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12851 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12851 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12851 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052171721127 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12851) ≤ 0.010534702411 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12851 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035596374201)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010534702411 + 2 * 0.737676 / 12851) := by gcongr
    _ ≤ (0.052171721127 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12851 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12851

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12851
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510316722 : ℝ) ≤ plow 12851 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12851) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578781890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363599849) : eMP 12851 0.011 xi bn ≤ 0.001174129131 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12851 : ℝ) * (1 - 0.011))) ≤ 0.000580566303 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363599849 / (12851 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580566303 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580566303 : ℝ) + 3.141593 * 0.052578781890 / (12851 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174129131 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578781890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363599849) : PiBarMP 12851 12 0.011 xi bn ≤ 0.160291263728 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12851 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036926952880 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.737034731271 : ℝ) ≤ √((12851 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.362251212650 : ℝ) ≤ √(12851 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12851) ≤ 0.122901654773 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036926952880 + 0.052578781890 * 1.772454 / (2 * (112.737034731271 : ℝ))) * (1 + 0.001174129131) +
        8 / (12851 * 113.362251212650) + 0.122901654773 := by gcongr
    _ ≤ (0.160291263728 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578781890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363599849) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281472357607) :
    parallelOracle 12851 0.011 xi bn cd ≤ 0.161269724981 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12851 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12851 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510316722 : ℝ) ≤ plow 12851 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.362251212650 : ℝ) ≤ √(12851 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281472357607 : ℝ) / (2 * 0.560510316722 * 113.362251212650)) * 0.160291263728 +
        0.281472357607 ^ 2 / (2 * 0.560510316722 * 113.362251212650) := by gcongr
    _ ≤ (0.161269724981 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578781890) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363599849)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281472357607) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12851 12851 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510316722 : ℝ) ≤ plow 12851 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.362251212650 : ℝ) ≤ √(12851 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12851 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12851 Θ 1.22 ≤ 0.011697901955 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.362251212650 := by gcongr <;> linarith
      _ ≤ (0.011697901955 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12851 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12851 12851 0.011 ≤ 0.008432145407 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12851 12851 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12851 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12851 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12851 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12851 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161269724981 + 0.011697901955 + (0.008432145407 : ℝ) *
        (1 + 2 * (0.281472357607 + 0.011697901955) / (0.560510316722 * 113.362251212650))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12851]

end BstLean.Part269.N12851

/-! The original eight local profiles supply actual 12851 moment certificates. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12851 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052578781890 ∧
    0 ≤ bN 12851 BstLean.Part154.csC (groupTheta g) ∧ bN 12851 BstLean.Part154.csC (groupTheta g) ≤ 0.001363599849 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12851 12851 0.011
      (momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12851 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12851 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12851 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229300636480 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12851 0.011
      (momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12851 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12851
/-! The actual computed-centre upper energy formula at 12851. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12851

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12851)
open BstLean.Part268 (cell12851)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085061652697
  | 2 => 0.085996787315
  | 3 => 0.086928993186
  | 4 => 0.087859439377
  | 5 => 0.088789547668
  | 6 => 0.089721031071
  | 7 => 0.090655936156
  | 8 => 0.091596689259
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12851 12851 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12851 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12851

/-! Actual upper energy certificates on all 43 source endpoints at 12851. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12851)
open BstLean.Part268 (cell12851)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12851 (gMinus 12851) (1 - (cell12851 i).lower) ≤ 1 ∧
    energyUpper 12851 (gMinus 12851) (BstLean.Part211.gPlus 12851)
      (finiteEnergy 12851 12851 0.011) (1 - (cell12851 i).lower) ≤
      (cell12851 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨10,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨11,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨12,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨13,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨14,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨15,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨16,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨17,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨18,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨19,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨20,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨21,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨22,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨23,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨24,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨25,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨26,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨27,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨28,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨29,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨30,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨31,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨32,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨33,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨34,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨35,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨36,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨37,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨38,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨39,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨40,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨41,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨42,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨43,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨44,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨45,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨46,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨47,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨48,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨49,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨50,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨51,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12851) (by norm_num)
        (q := 1 - (cell12851 ⟨52,by decide⟩).lower)
        (by norm_num [cell12851]) (by norm_num [cell12851])
      exact ⟨E.1,E.2.trans (by norm_num [cell12851])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12851

/-! Source-cell containment and simple scalar guards at 12851. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12851)
open BstLean.Part268 (cell12851)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12851 ⟨10,by decide⟩).lower ∧ (cell12851 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12851 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12851 ⟨11,by decide⟩).lower ∧ (cell12851 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12851 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12851 ⟨12,by decide⟩).lower ∧ (cell12851 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12851 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12851 ⟨13,by decide⟩).lower ∧ (cell12851 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12851 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12851 ⟨14,by decide⟩).lower ∧ (cell12851 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12851 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12851 ⟨15,by decide⟩).lower ∧ (cell12851 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12851 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12851 ⟨16,by decide⟩).lower ∧ (cell12851 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12851 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12851 ⟨17,by decide⟩).lower ∧ (cell12851 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12851 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12851 ⟨18,by decide⟩).lower ∧ (cell12851 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12851 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12851 ⟨19,by decide⟩).lower ∧ (cell12851 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12851 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12851 ⟨20,by decide⟩).lower ∧ (cell12851 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12851 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12851 ⟨21,by decide⟩).lower ∧ (cell12851 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12851 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12851 ⟨22,by decide⟩).lower ∧ (cell12851 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12851 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12851 ⟨23,by decide⟩).lower ∧ (cell12851 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12851 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12851 ⟨24,by decide⟩).lower ∧ (cell12851 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12851 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12851 ⟨25,by decide⟩).lower ∧ (cell12851 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12851 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12851 ⟨26,by decide⟩).lower ∧ (cell12851 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12851 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12851 ⟨27,by decide⟩).lower ∧ (cell12851 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12851 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12851 ⟨28,by decide⟩).lower ∧ (cell12851 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12851 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12851 ⟨29,by decide⟩).lower ∧ (cell12851 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12851 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12851 ⟨30,by decide⟩).lower ∧ (cell12851 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12851 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12851 ⟨31,by decide⟩).lower ∧ (cell12851 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12851 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12851 ⟨32,by decide⟩).lower ∧ (cell12851 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12851 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12851 ⟨33,by decide⟩).lower ∧ (cell12851 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12851 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12851 ⟨34,by decide⟩).lower ∧ (cell12851 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12851 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12851 ⟨35,by decide⟩).lower ∧ (cell12851 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12851 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12851 ⟨36,by decide⟩).lower ∧ (cell12851 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12851 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12851 ⟨37,by decide⟩).lower ∧ (cell12851 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12851 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12851 ⟨38,by decide⟩).lower ∧ (cell12851 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12851 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12851 ⟨39,by decide⟩).lower ∧ (cell12851 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12851 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12851 ⟨40,by decide⟩).lower ∧ (cell12851 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12851 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12851 ⟨41,by decide⟩).lower ∧ (cell12851 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12851 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12851 ⟨42,by decide⟩).lower ∧ (cell12851 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12851 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12851 ⟨43,by decide⟩).lower ∧ (cell12851 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12851 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12851 ⟨44,by decide⟩).lower ∧ (cell12851 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12851 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12851 ⟨45,by decide⟩).lower ∧ (cell12851 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12851 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12851 ⟨46,by decide⟩).lower ∧ (cell12851 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12851 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12851 ⟨47,by decide⟩).lower ∧ (cell12851 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12851 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12851 ⟨48,by decide⟩).lower ∧ (cell12851 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12851 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12851 ⟨49,by decide⟩).lower ∧ (cell12851 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12851 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12851 ⟨50,by decide⟩).lower ∧ (cell12851 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12851 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12851 ⟨51,by decide⟩).lower ∧ (cell12851 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12851 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12851 ⟨52,by decide⟩).lower ∧ (cell12851 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12851 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12851 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12851 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12851,cell12851,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12851 i).lower ∧
    (cell12851 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12851 i).upper ≤ (0.532 : ℝ) ∧
    (cell12851 i).centre ≤ (0.1 : ℝ) ∧ (cell12851 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12851 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12851 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12851

/-! The local source numeric instances at 12851 have no network premises. -/
namespace BstLean.Part269.N12851
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12851)
open BstLean.Part268 (cell12851)

noncomputable def sourceNumerics12851 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12851 (cell12851 i)
      scalarRow12851.M scalarRow12851.H scalarRow12851.xi := by
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
    energy_allowance := scalarRow12851.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12851]
    centre_nonneg := (scalarRow12851.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12851])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12851
/-! Actual 12852 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12852 ≤ (1.035594977208 : ℝ) := by
  have hr : (113.366661766147 : ℝ) ≤ √(12852 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.366661766147 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12852 12852 (11 / 1000) ≤
    (0.008431817351 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12852) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.366661766147 : ℝ) ≤ √(12852 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12852)
  have hdiv : K / √(12852 : ℝ) ≤ K / 113.366661766147 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.366661766147 ≤ (0.008431817351 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12852.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12852 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12852 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12852 := gPlus_lower 12852
end BstLean.Part269.N12852

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12852
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035594977207 : ℝ) ≤ wn 12852 := by
  have hn : √(12852 : ℝ) ≤ 113.366661766148 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12852 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.366661766148 ≤ 2 / √(12852 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248850404 : ℝ) ≤ rhoBar 12852 BstLean.Part154.csC ∧
    rhoBar 12852 BstLean.Part154.csC ≤ 0.000248850789 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035594977207 : ℝ) / (1.295212 * 12852) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035594977208 : ℝ) / (1.29521 * 12852) := by gcongr
      _ ≤ (0.000248850789 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12852 BstLean.Part154.csC) ≤ 0.000995465083 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12852 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) ≤ 0.000190073805 ∧
    cc1 (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) ≤ 0.000120945246 ∧
    cc2 (rhoBar 12852 BstLean.Part154.csC) ≤ 0.000070209669 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12852 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12852 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12852 BstLean.Part154.csC * nuR (rhoBar 12852 BstLean.Part154.csC)) ≤ 0.000497717060 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248850789 : ℝ) * 0.000995465083 := by gcongr
      _ ≤ (0.000497717060 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12852 BstLean.Part154.csC) * nuR (rhoBar 12852 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995465083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12852 BstLean.Part154.csC) * rhoBar 12852 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248850789 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248850789 / 2 + 0.399 * 0.000995465083 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190073805 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497717060 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120945246 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248850789 / 1.414213562 := by gcongr
      _ ≤ (0.000070209669 : ℝ) := by norm_num

end BstLean.Part269.N12852

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12852
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) ≤ 1.56020E-7 := by
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12852 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12852 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12852 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190073805 : ℝ) ^ 2 + 0.000120945246 ^ 2 + 3 * 0.000070209669 ^ 2 +
        2 * 0.797885 * 0.000190073805 * 0.000120945246 + 2 * 0.000190073805 * 0.000070209669 +
        4 * 0.797885 * 0.000120945246 * 0.000070209669 := by gcongr
    _ ≤ (1.56020E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12852 BstLean.Part154.csC Θ ≤ 0.002597119004 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12852 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12852 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12852 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035594977208 * 1.56020E-7 / (0.000248850404 : ℝ) := by gcongr
    _ ≤ 0.002597119004 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12852 BstLean.Part154.csC Θ ≤ 0.002881044150 + 0.000656249767 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12852 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12852 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035594977208 : ℝ) * ((2 * Θ * 0.000248850789 +
        (6863 / 10000) * 0.000248850789 * 12852 * 0.000995465083) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002881044150 + 0.000656249767 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12852 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12852 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12852 0.011 Θ ∧ gammaRatio 12852 0.011 Θ ≤ 0.000085548466 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12852 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035594977208 : ℝ) * 0.525 / ((1 - 0.011) * 12852) := by gcongr
      _ ≤ (0.000085548466 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12852 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12852 0.011 Θ) :=
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
    badAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12852 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12852 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12852 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12852 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12852 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12852 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12852 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12852 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12852 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12852 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035594977208 : ℝ) * 12852 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003363787312 + 0.003253368771 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12852

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12852
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12852 BstLean.Part154.csC) (piBar (rhoBar 12852 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12852 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12852 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12852 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12852 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12852 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12852 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12852 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12852 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12852 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12852 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052169669494 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12852) ≤ 0.010534292556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12852 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035594977208)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010534292556 + 2 * 0.737676 / 12852) := by gcongr
    _ ≤ (0.052169669494 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12852 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12852

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12852
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510360885 : ℝ) ≤ plow 12852 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12852) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578405917)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363487478) : eMP 12852 0.011 xi bn ≤ 0.001174035011 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12852 : ℝ) * (1 - 0.011))) ≤ 0.000580519795 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363487478 / (12852 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580519795 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580519795 : ℝ) + 3.141593 * 0.052578405917 / (12852 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001174035011 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578405917)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363487478) : PiBarMP 12852 12 0.011 xi bn ≤ 0.160284935651 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12852 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036925431318 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.741420959645 : ℝ) ≤ √((12852 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.366661766147 : ℝ) ≤ √(12852 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12852) ≤ 0.122896873258 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036925431318 + 0.052578405917 * 1.772454 / (2 * (112.741420959645 : ℝ))) * (1 + 0.001174035011) +
        8 / (12852 * 113.366661766147) + 0.122896873258 := by gcongr
    _ ≤ (0.160284935651 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578405917)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363487478) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281469486147) :
    parallelOracle 12852 0.011 xi bn cd ≤ 0.161263328403 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12852 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12852 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510360885 : ℝ) ≤ plow 12852 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.366661766147 : ℝ) ≤ √(12852 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281469486147 : ℝ) / (2 * 0.560510360885 * 113.366661766147)) * 0.160284935651 +
        0.281469486147 ^ 2 / (2 * 0.560510360885 * 113.366661766147) := by gcongr
    _ ≤ (0.161263328403 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578405917) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363487478)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281469486147) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12852 12852 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510360885 : ℝ) ≤ plow 12852 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.366661766147 : ℝ) ≤ √(12852 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12852 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12852 Θ 1.22 ≤ 0.011697446845 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.366661766147 := by gcongr <;> linarith
      _ ≤ (0.011697446845 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12852 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12852 12852 0.011 ≤ 0.008431817351 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12852 12852 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12852 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12852 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12852 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12852 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161263328403 + 0.011697446845 + (0.008431817351 : ℝ) *
        (1 + 2 * (0.281469486147 + 0.011697446845) / (0.560510360885 * 113.366661766147))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12852]

end BstLean.Part269.N12852

/-! The original eight local profiles supply actual 12852 moment certificates. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12852 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052578405917 ∧
    0 ≤ bN 12852 BstLean.Part154.csC (groupTheta g) ∧ bN 12852 BstLean.Part154.csC (groupTheta g) ≤ 0.001363487478 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12852 12852 0.011
      (momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12852 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12852 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12852 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229299816653 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12852 0.011
      (momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12852 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12852
/-! The actual computed-centre upper energy formula at 12852. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12852

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12852)
open BstLean.Part268 (cell12852)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085058888801
  | 2 => 0.085993975961
  | 3 => 0.086926127999
  | 4 => 0.087856512474
  | 5 => 0.088786549391
  | 6 => 0.089717949678
  | 7 => 0.090652757477
  | 8 => 0.091593396314
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12852 12852 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12852 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12852

/-! Actual upper energy certificates on all 43 source endpoints at 12852. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12852)
open BstLean.Part268 (cell12852)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12852 (gMinus 12852) (1 - (cell12852 i).lower) ≤ 1 ∧
    energyUpper 12852 (gMinus 12852) (BstLean.Part211.gPlus 12852)
      (finiteEnergy 12852 12852 0.011) (1 - (cell12852 i).lower) ≤
      (cell12852 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨10,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨11,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨12,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨13,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨14,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨15,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨16,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨17,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨18,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨19,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨20,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨21,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨22,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨23,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨24,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨25,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨26,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨27,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨28,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨29,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨30,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨31,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨32,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨33,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨34,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨35,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨36,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨37,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨38,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨39,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨40,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨41,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨42,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨43,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨44,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨45,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨46,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨47,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨48,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨49,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨50,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨51,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12852) (by norm_num)
        (q := 1 - (cell12852 ⟨52,by decide⟩).lower)
        (by norm_num [cell12852]) (by norm_num [cell12852])
      exact ⟨E.1,E.2.trans (by norm_num [cell12852])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12852

/-! Source-cell containment and simple scalar guards at 12852. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12852)
open BstLean.Part268 (cell12852)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12852 ⟨10,by decide⟩).lower ∧ (cell12852 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12852 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12852 ⟨11,by decide⟩).lower ∧ (cell12852 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12852 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12852 ⟨12,by decide⟩).lower ∧ (cell12852 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12852 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12852 ⟨13,by decide⟩).lower ∧ (cell12852 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12852 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12852 ⟨14,by decide⟩).lower ∧ (cell12852 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12852 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12852 ⟨15,by decide⟩).lower ∧ (cell12852 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12852 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12852 ⟨16,by decide⟩).lower ∧ (cell12852 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12852 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12852 ⟨17,by decide⟩).lower ∧ (cell12852 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12852 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12852 ⟨18,by decide⟩).lower ∧ (cell12852 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12852 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12852 ⟨19,by decide⟩).lower ∧ (cell12852 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12852 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12852 ⟨20,by decide⟩).lower ∧ (cell12852 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12852 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12852 ⟨21,by decide⟩).lower ∧ (cell12852 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12852 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12852 ⟨22,by decide⟩).lower ∧ (cell12852 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12852 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12852 ⟨23,by decide⟩).lower ∧ (cell12852 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12852 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12852 ⟨24,by decide⟩).lower ∧ (cell12852 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12852 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12852 ⟨25,by decide⟩).lower ∧ (cell12852 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12852 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12852 ⟨26,by decide⟩).lower ∧ (cell12852 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12852 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12852 ⟨27,by decide⟩).lower ∧ (cell12852 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12852 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12852 ⟨28,by decide⟩).lower ∧ (cell12852 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12852 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12852 ⟨29,by decide⟩).lower ∧ (cell12852 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12852 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12852 ⟨30,by decide⟩).lower ∧ (cell12852 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12852 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12852 ⟨31,by decide⟩).lower ∧ (cell12852 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12852 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12852 ⟨32,by decide⟩).lower ∧ (cell12852 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12852 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12852 ⟨33,by decide⟩).lower ∧ (cell12852 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12852 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12852 ⟨34,by decide⟩).lower ∧ (cell12852 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12852 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12852 ⟨35,by decide⟩).lower ∧ (cell12852 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12852 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12852 ⟨36,by decide⟩).lower ∧ (cell12852 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12852 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12852 ⟨37,by decide⟩).lower ∧ (cell12852 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12852 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12852 ⟨38,by decide⟩).lower ∧ (cell12852 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12852 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12852 ⟨39,by decide⟩).lower ∧ (cell12852 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12852 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12852 ⟨40,by decide⟩).lower ∧ (cell12852 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12852 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12852 ⟨41,by decide⟩).lower ∧ (cell12852 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12852 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12852 ⟨42,by decide⟩).lower ∧ (cell12852 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12852 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12852 ⟨43,by decide⟩).lower ∧ (cell12852 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12852 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12852 ⟨44,by decide⟩).lower ∧ (cell12852 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12852 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12852 ⟨45,by decide⟩).lower ∧ (cell12852 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12852 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12852 ⟨46,by decide⟩).lower ∧ (cell12852 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12852 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12852 ⟨47,by decide⟩).lower ∧ (cell12852 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12852 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12852 ⟨48,by decide⟩).lower ∧ (cell12852 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12852 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12852 ⟨49,by decide⟩).lower ∧ (cell12852 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12852 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12852 ⟨50,by decide⟩).lower ∧ (cell12852 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12852 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12852 ⟨51,by decide⟩).lower ∧ (cell12852 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12852 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12852 ⟨52,by decide⟩).lower ∧ (cell12852 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12852 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12852 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12852 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12852,cell12852,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12852 i).lower ∧
    (cell12852 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12852 i).upper ≤ (0.532 : ℝ) ∧
    (cell12852 i).centre ≤ (0.1 : ℝ) ∧ (cell12852 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12852 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12852 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12852

/-! The local source numeric instances at 12852 have no network premises. -/
namespace BstLean.Part269.N12852
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12852)
open BstLean.Part268 (cell12852)

noncomputable def sourceNumerics12852 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12852 (cell12852 i)
      scalarRow12852.M scalarRow12852.H scalarRow12852.xi := by
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
    energy_allowance := scalarRow12852.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12852]
    centre_nonneg := (scalarRow12852.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12852])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12852
/-! Actual 12853 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12853 ≤ (1.035593580378 : ℝ) := by
  have hr : (113.371072148057 : ℝ) ≤ √(12853 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.371072148057 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12853 12853 (11 / 1000) ≤
    (0.008431489332 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12853) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.371072148057 : ℝ) ≤ √(12853 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12853)
  have hdiv : K / √(12853 : ℝ) ≤ K / 113.371072148057 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.371072148057 ≤ (0.008431489332 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12853.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12853 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12853 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12853 := gPlus_lower 12853
end BstLean.Part269.N12853

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12853
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035593580377 : ℝ) ≤ wn 12853 := by
  have hn : √(12853 : ℝ) ≤ 113.371072148058 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12853 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.371072148058 ≤ 2 / √(12853 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248830707 : ℝ) ≤ rhoBar 12853 BstLean.Part154.csC ∧
    rhoBar 12853 BstLean.Part154.csC ≤ 0.000248831092 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035593580377 : ℝ) / (1.295212 * 12853) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035593580378 : ℝ) / (1.29521 * 12853) := by gcongr
      _ ≤ (0.000248831092 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12853 BstLean.Part154.csC) ≤ 0.000995386285 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12853 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) ≤ 0.000190058760 ∧
    cc1 (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) ≤ 0.000120935673 ∧
    cc2 (rhoBar 12853 BstLean.Part154.csC) ≤ 0.000070204111 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12853 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12853 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12853 BstLean.Part154.csC * nuR (rhoBar 12853 BstLean.Part154.csC)) ≤ 0.000497677664 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248831092 : ℝ) * 0.000995386285 := by gcongr
      _ ≤ (0.000497677664 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12853 BstLean.Part154.csC) * nuR (rhoBar 12853 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995386285 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12853 BstLean.Part154.csC) * rhoBar 12853 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248831092 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248831092 / 2 + 0.399 * 0.000995386285 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190058760 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497677664 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120935673 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248831092 / 1.414213562 := by gcongr
      _ ≤ (0.000070204111 : ℝ) := by norm_num

end BstLean.Part269.N12853

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12853
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) ≤ 1.55995E-7 := by
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12853 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12853 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12853 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190058760 : ℝ) ^ 2 + 0.000120935673 ^ 2 + 3 * 0.000070204111 ^ 2 +
        2 * 0.797885 * 0.000190058760 * 0.000120935673 + 2 * 0.000190058760 * 0.000070204111 +
        4 * 0.797885 * 0.000120935673 * 0.000070204111 := by gcongr
    _ ≤ (1.55995E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12853 BstLean.Part154.csC Θ ≤ 0.002596904901 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12853 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12853 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12853 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035593580378 * 1.55995E-7 / (0.000248830707 : ℝ) := by gcongr
    _ ≤ 0.002596904901 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12853 BstLean.Part154.csC Θ ≤ 0.002880808323 + 0.000656196939 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12853 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12853 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035593580378 : ℝ) * ((2 * Θ * 0.000248831092 +
        (6863 / 10000) * 0.000248831092 * 12853 * 0.000995386285) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002880808323 + 0.000656196939 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12853 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12853 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12853 0.011 Θ ∧ gammaRatio 12853 0.011 Θ ≤ 0.000085541695 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12853 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035593580378 : ℝ) * 0.525 / ((1 - 0.011) * 12853) := by gcongr
      _ ≤ (0.000085541695 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12853 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12853 0.011 Θ) :=
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
    badAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12853 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12853 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12853 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12853 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12853 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12853 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12853 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12853 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12853 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12853 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035593580378 : ℝ) * 12853 *
        (1.8602E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003363551485 + 0.003253101840 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12853

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12853
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12853 BstLean.Part154.csC) (piBar (rhoBar 12853 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12853 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12853 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12853 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12853 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12853 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12853 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12853 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12853 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12853 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12853 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052167618103 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12853) ≤ 0.010533882749 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12853 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035593580378)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010533882749 + 2 * 0.737676 / 12853) := by gcongr
    _ ≤ (0.052167618103 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12853 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12853

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12853
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510405041 : ℝ) ≤ plow 12853 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12853) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578029951)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363375074) : eMP 12853 0.011 xi bn ≤ 0.001173940883 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12853 : ℝ) * (1 - 0.011))) ≤ 0.000580473283 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363375074 / (12853 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580473283 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580473283 : ℝ) + 3.141593 * 0.052578029951 / (12853 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173940883 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578029951)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363375074) : PiBarMP 12853 12 0.011 xi bn ≤ 0.160278607625 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12853 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036923909246 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.745807017378 : ℝ) ≤ √((12853 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.371072148057 : ℝ) ≤ √(12853 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12853) ≤ 0.122892092302 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036923909246 + 0.052578029951 * 1.772454 / (2 * (112.745807017378 : ℝ))) * (1 + 0.001173940883) +
        8 / (12853 * 113.371072148057) + 0.122892092302 := by gcongr
    _ ≤ (0.160278607625 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578029951)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363375074) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281466614942) :
    parallelOracle 12853 0.011 xi bn cd ≤ 0.161256931885 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12853 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12853 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510405041 : ℝ) ≤ plow 12853 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.371072148057 : ℝ) ≤ √(12853 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281466614942 : ℝ) / (2 * 0.560510405041 * 113.371072148057)) * 0.160278607625 +
        0.281466614942 ^ 2 / (2 * 0.560510405041 * 113.371072148057) := by gcongr
    _ ≤ (0.161256931885 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052578029951) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363375074)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281466614942) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12853 12853 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510405041 : ℝ) ≤ plow 12853 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.371072148057 : ℝ) ≤ √(12853 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12853 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12853 Θ 1.22 ≤ 0.011696991789 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.371072148057 := by gcongr <;> linarith
      _ ≤ (0.011696991789 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12853 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12853 12853 0.011 ≤ 0.008431489332 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12853 12853 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12853 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12853 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12853 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12853 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161256931885 + 0.011696991789 + (0.008431489332 : ℝ) *
        (1 + 2 * (0.281466614942 + 0.011696991789) / (0.560510405041 * 113.371072148057))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12853]

end BstLean.Part269.N12853

/-! The original eight local profiles supply actual 12853 moment certificates. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12853 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052578029951 ∧
    0 ≤ bN 12853 BstLean.Part154.csC (groupTheta g) ∧ bN 12853 BstLean.Part154.csC (groupTheta g) ≤ 0.001363375074 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12853 12853 0.011
      (momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12853 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12853 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12853 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229298996839 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12853 0.011
      (momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12853 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12853
/-! The actual computed-centre upper energy formula at 12853. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12853

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12853)
open BstLean.Part268 (cell12853)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085056125837
  | 2 => 0.085991165577
  | 3 => 0.086923263825
  | 4 => 0.087853586640
  | 5 => 0.088783552251
  | 6 => 0.089714869505
  | 7 => 0.090649580120
  | 8 => 0.091590104811
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12853 12853 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12853 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12853

/-! Actual upper energy certificates on all 43 source endpoints at 12853. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12853)
open BstLean.Part268 (cell12853)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12853 (gMinus 12853) (1 - (cell12853 i).lower) ≤ 1 ∧
    energyUpper 12853 (gMinus 12853) (BstLean.Part211.gPlus 12853)
      (finiteEnergy 12853 12853 0.011) (1 - (cell12853 i).lower) ≤
      (cell12853 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨10,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨11,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨12,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨13,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨14,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨15,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨16,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨17,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨18,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨19,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨20,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨21,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨22,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨23,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨24,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨25,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨26,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨27,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨28,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨29,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨30,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨31,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨32,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨33,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨34,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨35,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨36,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨37,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨38,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨39,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨40,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨41,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨42,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨43,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨44,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨45,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨46,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨47,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨48,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨49,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨50,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨51,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12853) (by norm_num)
        (q := 1 - (cell12853 ⟨52,by decide⟩).lower)
        (by norm_num [cell12853]) (by norm_num [cell12853])
      exact ⟨E.1,E.2.trans (by norm_num [cell12853])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12853

/-! Source-cell containment and simple scalar guards at 12853. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12853)
open BstLean.Part268 (cell12853)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12853 ⟨10,by decide⟩).lower ∧ (cell12853 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12853 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12853 ⟨11,by decide⟩).lower ∧ (cell12853 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12853 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12853 ⟨12,by decide⟩).lower ∧ (cell12853 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12853 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12853 ⟨13,by decide⟩).lower ∧ (cell12853 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12853 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12853 ⟨14,by decide⟩).lower ∧ (cell12853 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12853 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12853 ⟨15,by decide⟩).lower ∧ (cell12853 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12853 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12853 ⟨16,by decide⟩).lower ∧ (cell12853 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12853 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12853 ⟨17,by decide⟩).lower ∧ (cell12853 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12853 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12853 ⟨18,by decide⟩).lower ∧ (cell12853 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12853 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12853 ⟨19,by decide⟩).lower ∧ (cell12853 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12853 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12853 ⟨20,by decide⟩).lower ∧ (cell12853 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12853 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12853 ⟨21,by decide⟩).lower ∧ (cell12853 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12853 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12853 ⟨22,by decide⟩).lower ∧ (cell12853 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12853 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12853 ⟨23,by decide⟩).lower ∧ (cell12853 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12853 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12853 ⟨24,by decide⟩).lower ∧ (cell12853 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12853 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12853 ⟨25,by decide⟩).lower ∧ (cell12853 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12853 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12853 ⟨26,by decide⟩).lower ∧ (cell12853 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12853 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12853 ⟨27,by decide⟩).lower ∧ (cell12853 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12853 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12853 ⟨28,by decide⟩).lower ∧ (cell12853 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12853 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12853 ⟨29,by decide⟩).lower ∧ (cell12853 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12853 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12853 ⟨30,by decide⟩).lower ∧ (cell12853 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12853 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12853 ⟨31,by decide⟩).lower ∧ (cell12853 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12853 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12853 ⟨32,by decide⟩).lower ∧ (cell12853 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12853 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12853 ⟨33,by decide⟩).lower ∧ (cell12853 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12853 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12853 ⟨34,by decide⟩).lower ∧ (cell12853 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12853 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12853 ⟨35,by decide⟩).lower ∧ (cell12853 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12853 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12853 ⟨36,by decide⟩).lower ∧ (cell12853 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12853 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12853 ⟨37,by decide⟩).lower ∧ (cell12853 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12853 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12853 ⟨38,by decide⟩).lower ∧ (cell12853 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12853 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12853 ⟨39,by decide⟩).lower ∧ (cell12853 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12853 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12853 ⟨40,by decide⟩).lower ∧ (cell12853 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12853 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12853 ⟨41,by decide⟩).lower ∧ (cell12853 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12853 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12853 ⟨42,by decide⟩).lower ∧ (cell12853 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12853 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12853 ⟨43,by decide⟩).lower ∧ (cell12853 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12853 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12853 ⟨44,by decide⟩).lower ∧ (cell12853 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12853 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12853 ⟨45,by decide⟩).lower ∧ (cell12853 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12853 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12853 ⟨46,by decide⟩).lower ∧ (cell12853 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12853 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12853 ⟨47,by decide⟩).lower ∧ (cell12853 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12853 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12853 ⟨48,by decide⟩).lower ∧ (cell12853 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12853 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12853 ⟨49,by decide⟩).lower ∧ (cell12853 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12853 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12853 ⟨50,by decide⟩).lower ∧ (cell12853 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12853 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12853 ⟨51,by decide⟩).lower ∧ (cell12853 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12853 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12853 ⟨52,by decide⟩).lower ∧ (cell12853 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12853 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12853 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12853 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12853,cell12853,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12853 i).lower ∧
    (cell12853 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12853 i).upper ≤ (0.532 : ℝ) ∧
    (cell12853 i).centre ≤ (0.1 : ℝ) ∧ (cell12853 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12853 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12853 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12853

/-! The local source numeric instances at 12853 have no network premises. -/
namespace BstLean.Part269.N12853
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12853)
open BstLean.Part268 (cell12853)

noncomputable def sourceNumerics12853 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12853 (cell12853 i)
      scalarRow12853.M scalarRow12853.H scalarRow12853.xi := by
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
    energy_allowance := scalarRow12853.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12853]
    centre_nonneg := (scalarRow12853.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12853])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12853
/-! Actual 12854 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12854 ≤ (1.035592183712 : ℝ) := by
  have hr : (113.375482358400 : ℝ) ≤ √(12854 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.375482358400 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12854 12854 (11 / 1000) ≤
    (0.008431161352 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12854) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.375482358400 : ℝ) ≤ √(12854 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12854)
  have hdiv : K / √(12854 : ℝ) ≤ K / 113.375482358400 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.375482358400 ≤ (0.008431161352 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12854.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12854 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12854 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12854 := gPlus_lower 12854
end BstLean.Part269.N12854

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12854
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035592183711 : ℝ) ≤ wn 12854 := by
  have hn : √(12854 : ℝ) ≤ 113.375482358401 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12854 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.375482358401 ≤ 2 / √(12854 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248811013 : ℝ) ≤ rhoBar 12854 BstLean.Part154.csC ∧
    rhoBar 12854 BstLean.Part154.csC ≤ 0.000248811398 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035592183711 : ℝ) / (1.295212 * 12854) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035592183712 : ℝ) / (1.29521 * 12854) := by gcongr
      _ ≤ (0.000248811398 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12854 BstLean.Part154.csC) ≤ 0.000995307500 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12854 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) ≤ 0.000190043717 ∧
    cc1 (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) ≤ 0.000120926101 ∧
    cc2 (rhoBar 12854 BstLean.Part154.csC) ≤ 0.000070198555 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12854 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12854 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12854 BstLean.Part154.csC * nuR (rhoBar 12854 BstLean.Part154.csC)) ≤ 0.000497638273 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248811398 : ℝ) * 0.000995307500 := by gcongr
      _ ≤ (0.000497638273 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12854 BstLean.Part154.csC) * nuR (rhoBar 12854 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995307500 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12854 BstLean.Part154.csC) * rhoBar 12854 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248811398 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248811398 / 2 + 0.399 * 0.000995307500 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190043717 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497638273 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120926101 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248811398 / 1.414213562 := by gcongr
      _ ≤ (0.000070198555 : ℝ) := by norm_num

end BstLean.Part269.N12854

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12854
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) ≤ 1.55971E-7 := by
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12854 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12854 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12854 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190043717 : ℝ) ^ 2 + 0.000120926101 ^ 2 + 3 * 0.000070198555 ^ 2 +
        2 * 0.797885 * 0.000190043717 * 0.000120926101 + 2 * 0.000190043717 * 0.000070198555 +
        4 * 0.797885 * 0.000120926101 * 0.000070198555 := by gcongr
    _ ≤ (1.55971E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12854 BstLean.Part154.csC Θ ≤ 0.002596707382 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12854 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12854 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12854 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035592183712 * 1.55971E-7 / (0.000248811013 : ℝ) := by gcongr
    _ ≤ 0.002596707382 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12854 BstLean.Part154.csC Θ ≤ 0.002880572534 + 0.000656144118 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12854 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12854 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035592183712 : ℝ) * ((2 * Θ * 0.000248811398 +
        (6863 / 10000) * 0.000248811398 * 12854 * 0.000995307500) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002880572534 + 0.000656144118 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12854 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12854 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12854 0.011 Θ ∧ gammaRatio 12854 0.011 Θ ≤ 0.000085534925 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12854 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035592183712 : ℝ) * 0.525 / ((1 - 0.011) * 12854) := by gcongr
      _ ≤ (0.000085534925 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12854 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12854 0.011 Θ) :=
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
    badAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12854 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12854 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12854 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12854 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12854 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12854 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12854 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12854 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12854 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12854 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035592183712 : ℝ) * 12854 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003363315696 + 0.003252851500 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12854

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12854
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12854 BstLean.Part154.csC) (piBar (rhoBar 12854 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12854 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12854 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12854 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12854 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12854 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12854 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12854 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12854 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12854 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12854 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052165566954 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12854) ≤ 0.010533472990 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12854 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035592183712)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010533472990 + 2 * 0.737676 / 12854) := by gcongr
    _ ≤ (0.052165566954 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12854 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12854

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12854
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510449190 : ℝ) ≤ plow 12854 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12854) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577662734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363271376) : eMP 12854 0.011 xi bn ≤ 0.001173850473 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12854 : ℝ) * (1 - 0.011))) ≤ 0.000580428629 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363271376 / (12854 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580428629 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580428629 : ℝ) + 3.141593 * 0.052577662734 / (12854 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173850473 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577662734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363271376) : PiBarMP 12854 12 0.011 xi bn ≤ 0.160272398339 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12854 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036922505008 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.750192904491 : ℝ) ≤ √((12854 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.375482358400 : ℝ) ≤ √(12854 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12854) ≤ 0.122887311904 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036922505008 + 0.052577662734 * 1.772454 / (2 * (112.750192904491 : ℝ))) * (1 + 0.001173850473) +
        8 / (12854 * 113.375482358400) + 0.122887311904 := by gcongr
    _ ≤ (0.160272398339 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577662734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363271376) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281463763053) :
    parallelOracle 12854 0.011 xi bn cd ≤ 0.161250654487 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12854 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12854 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510449190 : ℝ) ≤ plow 12854 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.375482358400 : ℝ) ≤ √(12854 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281463763053 : ℝ) / (2 * 0.560510449190 * 113.375482358400)) * 0.160272398339 +
        0.281463763053 ^ 2 / (2 * 0.560510449190 * 113.375482358400) := by gcongr
    _ ≤ (0.161250654487 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577662734) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363271376)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281463763053) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12854 12854 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510449190 : ℝ) ≤ plow 12854 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.375482358400 : ℝ) ≤ √(12854 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12854 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12854 Θ 1.22 ≤ 0.011696536786 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.375482358400 := by gcongr <;> linarith
      _ ≤ (0.011696536786 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12854 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12854 12854 0.011 ≤ 0.008431161352 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12854 12854 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12854 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12854 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12854 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12854 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161250654487 + 0.011696536786 + (0.008431161352 : ℝ) *
        (1 + 2 * (0.281463763053 + 0.011696536786) / (0.560510449190 * 113.375482358400))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12854]

end BstLean.Part269.N12854

/-! The original eight local profiles supply actual 12854 moment certificates. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12854 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052577662734 ∧
    0 ≤ bN 12854 BstLean.Part154.csC (groupTheta g) ∧ bN 12854 BstLean.Part154.csC (groupTheta g) ≤ 0.001363271376 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12854 12854 0.011
      (momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12854 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12854 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12854 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229298196099 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12854 0.011
      (momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12854 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12854
/-! The actual computed-centre upper energy formula at 12854. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12854

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12854)
open BstLean.Part268 (cell12854)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085053363805
  | 2 => 0.085988356160
  | 3 => 0.086920400664
  | 4 => 0.087850661875
  | 5 => 0.088780556248
  | 6 => 0.089711790551
  | 7 => 0.090646404081
  | 8 => 0.091586814748
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12854 12854 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12854 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12854

/-! Actual upper energy certificates on all 43 source endpoints at 12854. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12854)
open BstLean.Part268 (cell12854)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12854 (gMinus 12854) (1 - (cell12854 i).lower) ≤ 1 ∧
    energyUpper 12854 (gMinus 12854) (BstLean.Part211.gPlus 12854)
      (finiteEnergy 12854 12854 0.011) (1 - (cell12854 i).lower) ≤
      (cell12854 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨10,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨11,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨12,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨13,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨14,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨15,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨16,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨17,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨18,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨19,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨20,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨21,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨22,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨23,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨24,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨25,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨26,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨27,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨28,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨29,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨30,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨31,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨32,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨33,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨34,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨35,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨36,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨37,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨38,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨39,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨40,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨41,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨42,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨43,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨44,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨45,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨46,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨47,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨48,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨49,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨50,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨51,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12854) (by norm_num)
        (q := 1 - (cell12854 ⟨52,by decide⟩).lower)
        (by norm_num [cell12854]) (by norm_num [cell12854])
      exact ⟨E.1,E.2.trans (by norm_num [cell12854])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12854

/-! Source-cell containment and simple scalar guards at 12854. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12854)
open BstLean.Part268 (cell12854)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12854 ⟨10,by decide⟩).lower ∧ (cell12854 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12854 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12854 ⟨11,by decide⟩).lower ∧ (cell12854 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12854 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12854 ⟨12,by decide⟩).lower ∧ (cell12854 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12854 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12854 ⟨13,by decide⟩).lower ∧ (cell12854 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12854 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12854 ⟨14,by decide⟩).lower ∧ (cell12854 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12854 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12854 ⟨15,by decide⟩).lower ∧ (cell12854 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12854 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12854 ⟨16,by decide⟩).lower ∧ (cell12854 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12854 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12854 ⟨17,by decide⟩).lower ∧ (cell12854 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12854 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12854 ⟨18,by decide⟩).lower ∧ (cell12854 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12854 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12854 ⟨19,by decide⟩).lower ∧ (cell12854 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12854 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12854 ⟨20,by decide⟩).lower ∧ (cell12854 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12854 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12854 ⟨21,by decide⟩).lower ∧ (cell12854 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12854 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12854 ⟨22,by decide⟩).lower ∧ (cell12854 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12854 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12854 ⟨23,by decide⟩).lower ∧ (cell12854 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12854 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12854 ⟨24,by decide⟩).lower ∧ (cell12854 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12854 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12854 ⟨25,by decide⟩).lower ∧ (cell12854 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12854 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12854 ⟨26,by decide⟩).lower ∧ (cell12854 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12854 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12854 ⟨27,by decide⟩).lower ∧ (cell12854 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12854 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12854 ⟨28,by decide⟩).lower ∧ (cell12854 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12854 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12854 ⟨29,by decide⟩).lower ∧ (cell12854 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12854 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12854 ⟨30,by decide⟩).lower ∧ (cell12854 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12854 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12854 ⟨31,by decide⟩).lower ∧ (cell12854 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12854 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12854 ⟨32,by decide⟩).lower ∧ (cell12854 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12854 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12854 ⟨33,by decide⟩).lower ∧ (cell12854 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12854 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12854 ⟨34,by decide⟩).lower ∧ (cell12854 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12854 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12854 ⟨35,by decide⟩).lower ∧ (cell12854 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12854 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12854 ⟨36,by decide⟩).lower ∧ (cell12854 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12854 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12854 ⟨37,by decide⟩).lower ∧ (cell12854 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12854 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12854 ⟨38,by decide⟩).lower ∧ (cell12854 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12854 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12854 ⟨39,by decide⟩).lower ∧ (cell12854 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12854 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12854 ⟨40,by decide⟩).lower ∧ (cell12854 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12854 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12854 ⟨41,by decide⟩).lower ∧ (cell12854 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12854 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12854 ⟨42,by decide⟩).lower ∧ (cell12854 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12854 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12854 ⟨43,by decide⟩).lower ∧ (cell12854 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12854 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12854 ⟨44,by decide⟩).lower ∧ (cell12854 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12854 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12854 ⟨45,by decide⟩).lower ∧ (cell12854 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12854 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12854 ⟨46,by decide⟩).lower ∧ (cell12854 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12854 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12854 ⟨47,by decide⟩).lower ∧ (cell12854 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12854 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12854 ⟨48,by decide⟩).lower ∧ (cell12854 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12854 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12854 ⟨49,by decide⟩).lower ∧ (cell12854 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12854 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12854 ⟨50,by decide⟩).lower ∧ (cell12854 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12854 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12854 ⟨51,by decide⟩).lower ∧ (cell12854 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12854 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12854 ⟨52,by decide⟩).lower ∧ (cell12854 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12854 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12854 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12854 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12854,cell12854,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12854 i).lower ∧
    (cell12854 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12854 i).upper ≤ (0.532 : ℝ) ∧
    (cell12854 i).centre ≤ (0.1 : ℝ) ∧ (cell12854 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12854 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12854 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12854

/-! The local source numeric instances at 12854 have no network premises. -/
namespace BstLean.Part269.N12854
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12854)
open BstLean.Part268 (cell12854)

noncomputable def sourceNumerics12854 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12854 (cell12854 i)
      scalarRow12854.M scalarRow12854.H scalarRow12854.xi := by
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
    energy_allowance := scalarRow12854.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12854]
    centre_nonneg := (scalarRow12854.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12854])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12854
/-! Actual 12855 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12855 ≤ (1.035590787211 : ℝ) := by
  have hr : (113.379892397197 : ℝ) ≤ √(12855 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.379892397197 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12855 12855 (11 / 1000) ≤
    (0.008430833410 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12855) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.379892397197 : ℝ) ≤ √(12855 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12855)
  have hdiv : K / √(12855 : ℝ) ≤ K / 113.379892397197 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.379892397197 ≤ (0.008430833410 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12855.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12855 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12855 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12855 := gPlus_lower 12855
end BstLean.Part269.N12855

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12855
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035590787210 : ℝ) ≤ wn 12855 := by
  have hn : √(12855 : ℝ) ≤ 113.379892397198 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12855 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.379892397198 ≤ 2 / √(12855 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248791322 : ℝ) ≤ rhoBar 12855 BstLean.Part154.csC ∧
    rhoBar 12855 BstLean.Part154.csC ≤ 0.000248791707 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035590787210 : ℝ) / (1.295212 * 12855) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035590787211 : ℝ) / (1.29521 * 12855) := by gcongr
      _ ≤ (0.000248791707 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12855 BstLean.Part154.csC) ≤ 0.000995228726 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12855 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) ≤ 0.000190028676 ∧
    cc1 (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) ≤ 0.000120916531 ∧
    cc2 (rhoBar 12855 BstLean.Part154.csC) ≤ 0.000070192999 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12855 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12855 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12855 BstLean.Part154.csC * nuR (rhoBar 12855 BstLean.Part154.csC)) ≤ 0.000497598889 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248791707 : ℝ) * 0.000995228726 := by gcongr
      _ ≤ (0.000497598889 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12855 BstLean.Part154.csC) * nuR (rhoBar 12855 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995228726 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12855 BstLean.Part154.csC) * rhoBar 12855 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248791707 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248791707 / 2 + 0.399 * 0.000995228726 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190028676 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497598889 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120916531 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248791707 / 1.414213562 := by gcongr
      _ ≤ (0.000070192999 : ℝ) := by norm_num

end BstLean.Part269.N12855

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12855
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) ≤ 1.55946E-7 := by
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12855 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12855 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12855 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190028676 : ℝ) ^ 2 + 0.000120916531 ^ 2 + 3 * 0.000070192999 ^ 2 +
        2 * 0.797885 * 0.000190028676 * 0.000120916531 + 2 * 0.000190028676 * 0.000070192999 +
        4 * 0.797885 * 0.000120916531 * 0.000070192999 := by gcongr
    _ ≤ (1.55946E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12855 BstLean.Part154.csC Θ ≤ 0.002596493152 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12855 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12855 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12855 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035590787211 * 1.55946E-7 / (0.000248791322 : ℝ) := by gcongr
    _ ≤ 0.002596493152 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12855 BstLean.Part154.csC Θ ≤ 0.002880336779 + 0.000656091306 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12855 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12855 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035590787211 : ℝ) * ((2 * Θ * 0.000248791707 +
        (6863 / 10000) * 0.000248791707 * 12855 * 0.000995228726) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002880336779 + 0.000656091306 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12855 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12855 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12855 0.011 Θ ∧ gammaRatio 12855 0.011 Θ ≤ 0.000085528156 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12855 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035590787211 : ℝ) * 0.525 / ((1 - 0.011) * 12855) := by gcongr
      _ ≤ (0.000085528156 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12855 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12855 0.011 Θ) :=
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
    badAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12855 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12855 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12855 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12855 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12855 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12855 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12855 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12855 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12855 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12855 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035590787211 : ℝ) * 12855 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003363079941 + 0.003252584458 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12855

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12855
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12855 BstLean.Part154.csC) (piBar (rhoBar 12855 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12855 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12855 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12855 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12855 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12855 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12855 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12855 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12855 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12855 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12855 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052163516042 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12855) ≤ 0.010533063278 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12855 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035590787211)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010533063278 + 2 * 0.737676 / 12855) := by gcongr
    _ ≤ (0.052163516042 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12855 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12855

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12855
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510493333 : ℝ) ≤ plow 12855 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12855) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577286782)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363158905) : eMP 12855 0.011 xi bn ≤ 0.001173756331 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12855 : ℝ) * (1 - 0.011))) ≤ 0.000580382110 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363158905 / (12855 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580382110 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580382110 : ℝ) + 3.141593 * 0.052577286782 / (12855 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173756331 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577286782)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363158905) : PiBarMP 12855 12 0.011 xi bn ≤ 0.160266070403 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12855 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036920981908 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.754578621003 : ℝ) ≤ √((12855 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.379892397197 : ℝ) ≤ √(12855 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12855) ≤ 0.122882532063 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036920981908 + 0.052577286782 * 1.772454 / (2 * (112.754578621003 : ℝ))) * (1 + 0.001173756331) +
        8 / (12855 * 113.379892397197) + 0.122882532063 := by gcongr
    _ ≤ (0.160266070403 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577286782)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363158905) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281460892351) :
    parallelOracle 12855 0.011 xi bn cd ≤ 0.161244258077 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12855 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12855 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510493333 : ℝ) ≤ plow 12855 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.379892397197 : ℝ) ≤ √(12855 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281460892351 : ℝ) / (2 * 0.560510493333 * 113.379892397197)) * 0.160266070403 +
        0.281460892351 ^ 2 / (2 * 0.560510493333 * 113.379892397197) := by gcongr
    _ ≤ (0.161244258077 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052577286782) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363158905)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281460892351) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12855 12855 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510493333 : ℝ) ≤ plow 12855 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.379892397197 : ℝ) ≤ √(12855 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12855 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12855 Θ 1.22 ≤ 0.011696081836 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.379892397197 := by gcongr <;> linarith
      _ ≤ (0.011696081836 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12855 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12855 12855 0.011 ≤ 0.008430833410 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12855 12855 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12855 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12855 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12855 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12855 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161244258077 + 0.011696081836 + (0.008430833410 : ℝ) *
        (1 + 2 * (0.281460892351 + 0.011696081836) / (0.560510493333 * 113.379892397197))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12855]

end BstLean.Part269.N12855

/-! The original eight local profiles supply actual 12855 moment certificates. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12855 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052577286782 ∧
    0 ≤ bN 12855 BstLean.Part154.csC (groupTheta g) ∧ bN 12855 BstLean.Part154.csC (groupTheta g) ≤ 0.001363158905 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12855 12855 0.011
      (momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12855 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12855 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12855 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229297376309 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12855 0.011
      (momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12855 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12855
/-! The actual computed-centre upper energy formula at 12855. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12855

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12855)
open BstLean.Part268 (cell12855)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085050602703
  | 2 => 0.085985547710
  | 3 => 0.086917538516
  | 4 => 0.087847738177
  | 5 => 0.088777561380
  | 6 => 0.089708712816
  | 7 => 0.090643229361
  | 8 => 0.091583526124
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12855 12855 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12855 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12855

/-! Actual upper energy certificates on all 43 source endpoints at 12855. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12855)
open BstLean.Part268 (cell12855)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12855 (gMinus 12855) (1 - (cell12855 i).lower) ≤ 1 ∧
    energyUpper 12855 (gMinus 12855) (BstLean.Part211.gPlus 12855)
      (finiteEnergy 12855 12855 0.011) (1 - (cell12855 i).lower) ≤
      (cell12855 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨10,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨11,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨12,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨13,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨14,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨15,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨16,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨17,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨18,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨19,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨20,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨21,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨22,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨23,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨24,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨25,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨26,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨27,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨28,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨29,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨30,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨31,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨32,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨33,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨34,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨35,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨36,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨37,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨38,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨39,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨40,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨41,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨42,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨43,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨44,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨45,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨46,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨47,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨48,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨49,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨50,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨51,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12855) (by norm_num)
        (q := 1 - (cell12855 ⟨52,by decide⟩).lower)
        (by norm_num [cell12855]) (by norm_num [cell12855])
      exact ⟨E.1,E.2.trans (by norm_num [cell12855])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12855

/-! Source-cell containment and simple scalar guards at 12855. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12855)
open BstLean.Part268 (cell12855)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12855 ⟨10,by decide⟩).lower ∧ (cell12855 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12855 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12855 ⟨11,by decide⟩).lower ∧ (cell12855 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12855 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12855 ⟨12,by decide⟩).lower ∧ (cell12855 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12855 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12855 ⟨13,by decide⟩).lower ∧ (cell12855 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12855 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12855 ⟨14,by decide⟩).lower ∧ (cell12855 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12855 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12855 ⟨15,by decide⟩).lower ∧ (cell12855 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12855 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12855 ⟨16,by decide⟩).lower ∧ (cell12855 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12855 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12855 ⟨17,by decide⟩).lower ∧ (cell12855 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12855 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12855 ⟨18,by decide⟩).lower ∧ (cell12855 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12855 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12855 ⟨19,by decide⟩).lower ∧ (cell12855 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12855 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12855 ⟨20,by decide⟩).lower ∧ (cell12855 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12855 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12855 ⟨21,by decide⟩).lower ∧ (cell12855 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12855 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12855 ⟨22,by decide⟩).lower ∧ (cell12855 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12855 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12855 ⟨23,by decide⟩).lower ∧ (cell12855 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12855 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12855 ⟨24,by decide⟩).lower ∧ (cell12855 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12855 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12855 ⟨25,by decide⟩).lower ∧ (cell12855 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12855 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12855 ⟨26,by decide⟩).lower ∧ (cell12855 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12855 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12855 ⟨27,by decide⟩).lower ∧ (cell12855 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12855 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12855 ⟨28,by decide⟩).lower ∧ (cell12855 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12855 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12855 ⟨29,by decide⟩).lower ∧ (cell12855 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12855 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12855 ⟨30,by decide⟩).lower ∧ (cell12855 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12855 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12855 ⟨31,by decide⟩).lower ∧ (cell12855 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12855 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12855 ⟨32,by decide⟩).lower ∧ (cell12855 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12855 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12855 ⟨33,by decide⟩).lower ∧ (cell12855 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12855 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12855 ⟨34,by decide⟩).lower ∧ (cell12855 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12855 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12855 ⟨35,by decide⟩).lower ∧ (cell12855 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12855 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12855 ⟨36,by decide⟩).lower ∧ (cell12855 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12855 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12855 ⟨37,by decide⟩).lower ∧ (cell12855 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12855 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12855 ⟨38,by decide⟩).lower ∧ (cell12855 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12855 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12855 ⟨39,by decide⟩).lower ∧ (cell12855 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12855 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12855 ⟨40,by decide⟩).lower ∧ (cell12855 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12855 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12855 ⟨41,by decide⟩).lower ∧ (cell12855 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12855 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12855 ⟨42,by decide⟩).lower ∧ (cell12855 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12855 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12855 ⟨43,by decide⟩).lower ∧ (cell12855 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12855 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12855 ⟨44,by decide⟩).lower ∧ (cell12855 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12855 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12855 ⟨45,by decide⟩).lower ∧ (cell12855 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12855 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12855 ⟨46,by decide⟩).lower ∧ (cell12855 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12855 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12855 ⟨47,by decide⟩).lower ∧ (cell12855 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12855 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12855 ⟨48,by decide⟩).lower ∧ (cell12855 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12855 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12855 ⟨49,by decide⟩).lower ∧ (cell12855 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12855 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12855 ⟨50,by decide⟩).lower ∧ (cell12855 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12855 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12855 ⟨51,by decide⟩).lower ∧ (cell12855 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12855 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12855 ⟨52,by decide⟩).lower ∧ (cell12855 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12855 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12855 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12855 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12855,cell12855,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12855 i).lower ∧
    (cell12855 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12855 i).upper ≤ (0.532 : ℝ) ∧
    (cell12855 i).centre ≤ (0.1 : ℝ) ∧ (cell12855 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12855 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12855 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12855

/-! The local source numeric instances at 12855 have no network premises. -/
namespace BstLean.Part269.N12855
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12855)
open BstLean.Part268 (cell12855)

noncomputable def sourceNumerics12855 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12855 (cell12855 i)
      scalarRow12855.M scalarRow12855.H scalarRow12855.xi := by
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
    energy_allowance := scalarRow12855.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12855]
    centre_nonneg := (scalarRow12855.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12855])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12855
/-! Actual 12856 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12856 ≤ (1.035589390873 : ℝ) := by
  have hr : (113.384302264466 : ℝ) ≤ √(12856 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.384302264466 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12856 12856 (11 / 1000) ≤
    (0.008430505506 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12856) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.384302264466 : ℝ) ≤ √(12856 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12856)
  have hdiv : K / √(12856 : ℝ) ≤ K / 113.384302264466 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.384302264466 ≤ (0.008430505506 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12856.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12856 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12856 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12856 := gPlus_lower 12856
end BstLean.Part269.N12856

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12856
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035589390872 : ℝ) ≤ wn 12856 := by
  have hn : √(12856 : ℝ) ≤ 113.384302264467 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12856 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.384302264467 ≤ 2 / √(12856 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248771635 : ℝ) ≤ rhoBar 12856 BstLean.Part154.csC ∧
    rhoBar 12856 BstLean.Part154.csC ≤ 0.000248772020 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035589390872 : ℝ) / (1.295212 * 12856) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035589390873 : ℝ) / (1.29521 * 12856) := by gcongr
      _ ≤ (0.000248772020 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12856 BstLean.Part154.csC) ≤ 0.000995149968 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12856 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) ≤ 0.000190013638 ∧
    cc1 (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) ≤ 0.000120906962 ∧
    cc2 (rhoBar 12856 BstLean.Part154.csC) ≤ 0.000070187445 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12856 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12856 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12856 BstLean.Part154.csC * nuR (rhoBar 12856 BstLean.Part154.csC)) ≤ 0.000497559512 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248772020 : ℝ) * 0.000995149968 := by gcongr
      _ ≤ (0.000497559512 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12856 BstLean.Part154.csC) * nuR (rhoBar 12856 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995149968 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12856 BstLean.Part154.csC) * rhoBar 12856 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248772020 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248772020 / 2 + 0.399 * 0.000995149968 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190013638 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497559512 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120906962 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248772020 / 1.414213562 := by gcongr
      _ ≤ (0.000070187445 : ℝ) := by norm_num

end BstLean.Part269.N12856

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12856
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) ≤ 1.55921E-7 := by
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12856 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12856 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12856 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190013638 : ℝ) ^ 2 + 0.000120906962 ^ 2 + 3 * 0.000070187445 ^ 2 +
        2 * 0.797885 * 0.000190013638 * 0.000120906962 + 2 * 0.000190013638 * 0.000070187445 +
        4 * 0.797885 * 0.000120906962 * 0.000070187445 := by gcongr
    _ ≤ (1.55921E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12856 BstLean.Part154.csC Θ ≤ 0.002596278847 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12856 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12856 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12856 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035589390873 * 1.55921E-7 / (0.000248771635 : ℝ) := by gcongr
    _ ≤ 0.002596278847 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12856 BstLean.Part154.csC Θ ≤ 0.002880101082 + 0.000656038505 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12856 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12856 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035589390873 : ℝ) * ((2 * Θ * 0.000248772020 +
        (6863 / 10000) * 0.000248772020 * 12856 * 0.000995149968) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002880101082 + 0.000656038505 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12856 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12856 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12856 0.011 Θ ∧ gammaRatio 12856 0.011 Θ ≤ 0.000085521388 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12856 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035589390873 : ℝ) * 0.525 / ((1 - 0.011) * 12856) := by gcongr
      _ ≤ (0.000085521388 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12856 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12856 0.011 Θ) :=
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
    badAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12856 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12856 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12856 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12856 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12856 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12856 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12856 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12856 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12856 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12856 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035589390873 : ℝ) * 12856 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003362844244 + 0.003252317352 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12856

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12856
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12856 BstLean.Part154.csC) (piBar (rhoBar 12856 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12856 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12856 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12856 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12856 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12856 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12856 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12856 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12856 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12856 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12856 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052161465377 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12856) ≤ 0.010532653615 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12856 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035589390873)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010532653615 + 2 * 0.737676 / 12856) := by gcongr
    _ ≤ (0.052161465377 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12856 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12856

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12856
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510537468 : ℝ) ≤ plow 12856 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12856) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576910854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363046395) : eMP 12856 0.011 xi bn ≤ 0.001173662180 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12856 : ℝ) * (1 - 0.011))) ≤ 0.000580335586 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001363046395 / (12856 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580335586 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580335586 : ℝ) + 3.141593 * 0.052576910854 / (12856 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173662180 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576910854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363046395) : PiBarMP 12856 12 0.011 xi bn ≤ 0.160259742436 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12856 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036919458217 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.758964166934 : ℝ) ≤ √((12856 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.384302264466 : ℝ) ≤ √(12856 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12856) ≤ 0.122877752780 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036919458217 + 0.052576910854 * 1.772454 / (2 * (112.758964166934 : ℝ))) * (1 + 0.001173662180) +
        8 / (12856 * 113.384302264466) + 0.122877752780 := by gcongr
    _ ≤ (0.160259742436 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576910854)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363046395) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281458021946) :
    parallelOracle 12856 0.011 xi bn cd ≤ 0.161237861644 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12856 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12856 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510537468 : ℝ) ≤ plow 12856 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.384302264466 : ℝ) ≤ √(12856 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281458021946 : ℝ) / (2 * 0.560510537468 * 113.384302264466)) * 0.160259742436 +
        0.281458021946 ^ 2 / (2 * 0.560510537468 * 113.384302264466) := by gcongr
    _ ≤ (0.161237861644 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576910854) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001363046395)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281458021946) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12856 12856 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510537468 : ℝ) ≤ plow 12856 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.384302264466 : ℝ) ≤ √(12856 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12856 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12856 Θ 1.22 ≤ 0.011695626939 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.384302264466 := by gcongr <;> linarith
      _ ≤ (0.011695626939 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12856 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12856 12856 0.011 ≤ 0.008430505506 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12856 12856 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12856 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12856 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12856 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12856 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161237861644 + 0.011695626939 + (0.008430505506 : ℝ) *
        (1 + 2 * (0.281458021946 + 0.011695626939) / (0.560510537468 * 113.384302264466))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12856]

end BstLean.Part269.N12856

/-! The original eight local profiles supply actual 12856 moment certificates. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12856 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052576910854 ∧
    0 ≤ bN 12856 BstLean.Part154.csC (groupTheta g) ∧ bN 12856 BstLean.Part154.csC (groupTheta g) ≤ 0.001363046395 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12856 12856 0.011
      (momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12856 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12856 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12856 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229296556569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12856 0.011
      (momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12856 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12856
/-! The actual computed-centre upper energy formula at 12856. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12856

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12856)
open BstLean.Part268 (cell12856)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085047842531
  | 2 => 0.085982740226
  | 3 => 0.086914677378
  | 4 => 0.087844815546
  | 5 => 0.088774567646
  | 6 => 0.089705636297
  | 7 => 0.090640055957
  | 8 => 0.091580238937
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12856 12856 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12856 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12856

/-! Actual upper energy certificates on all 43 source endpoints at 12856. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12856)
open BstLean.Part268 (cell12856)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12856 (gMinus 12856) (1 - (cell12856 i).lower) ≤ 1 ∧
    energyUpper 12856 (gMinus 12856) (BstLean.Part211.gPlus 12856)
      (finiteEnergy 12856 12856 0.011) (1 - (cell12856 i).lower) ≤
      (cell12856 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨10,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨11,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨12,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨13,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨14,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨15,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨16,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨17,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨18,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨19,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨20,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨21,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨22,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨23,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨24,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨25,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨26,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨27,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨28,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨29,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨30,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨31,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨32,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨33,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨34,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨35,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨36,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨37,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨38,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨39,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨40,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨41,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨42,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨43,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨44,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨45,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨46,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨47,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨48,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨49,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨50,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨51,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12856) (by norm_num)
        (q := 1 - (cell12856 ⟨52,by decide⟩).lower)
        (by norm_num [cell12856]) (by norm_num [cell12856])
      exact ⟨E.1,E.2.trans (by norm_num [cell12856])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12856

/-! Source-cell containment and simple scalar guards at 12856. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12856)
open BstLean.Part268 (cell12856)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12856 ⟨10,by decide⟩).lower ∧ (cell12856 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12856 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12856 ⟨11,by decide⟩).lower ∧ (cell12856 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12856 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12856 ⟨12,by decide⟩).lower ∧ (cell12856 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12856 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12856 ⟨13,by decide⟩).lower ∧ (cell12856 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12856 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12856 ⟨14,by decide⟩).lower ∧ (cell12856 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12856 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12856 ⟨15,by decide⟩).lower ∧ (cell12856 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12856 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12856 ⟨16,by decide⟩).lower ∧ (cell12856 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12856 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12856 ⟨17,by decide⟩).lower ∧ (cell12856 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12856 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12856 ⟨18,by decide⟩).lower ∧ (cell12856 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12856 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12856 ⟨19,by decide⟩).lower ∧ (cell12856 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12856 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12856 ⟨20,by decide⟩).lower ∧ (cell12856 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12856 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12856 ⟨21,by decide⟩).lower ∧ (cell12856 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12856 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12856 ⟨22,by decide⟩).lower ∧ (cell12856 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12856 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12856 ⟨23,by decide⟩).lower ∧ (cell12856 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12856 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12856 ⟨24,by decide⟩).lower ∧ (cell12856 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12856 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12856 ⟨25,by decide⟩).lower ∧ (cell12856 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12856 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12856 ⟨26,by decide⟩).lower ∧ (cell12856 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12856 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12856 ⟨27,by decide⟩).lower ∧ (cell12856 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12856 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12856 ⟨28,by decide⟩).lower ∧ (cell12856 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12856 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12856 ⟨29,by decide⟩).lower ∧ (cell12856 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12856 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12856 ⟨30,by decide⟩).lower ∧ (cell12856 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12856 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12856 ⟨31,by decide⟩).lower ∧ (cell12856 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12856 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12856 ⟨32,by decide⟩).lower ∧ (cell12856 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12856 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12856 ⟨33,by decide⟩).lower ∧ (cell12856 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12856 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12856 ⟨34,by decide⟩).lower ∧ (cell12856 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12856 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12856 ⟨35,by decide⟩).lower ∧ (cell12856 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12856 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12856 ⟨36,by decide⟩).lower ∧ (cell12856 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12856 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12856 ⟨37,by decide⟩).lower ∧ (cell12856 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12856 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12856 ⟨38,by decide⟩).lower ∧ (cell12856 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12856 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12856 ⟨39,by decide⟩).lower ∧ (cell12856 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12856 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12856 ⟨40,by decide⟩).lower ∧ (cell12856 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12856 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12856 ⟨41,by decide⟩).lower ∧ (cell12856 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12856 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12856 ⟨42,by decide⟩).lower ∧ (cell12856 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12856 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12856 ⟨43,by decide⟩).lower ∧ (cell12856 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12856 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12856 ⟨44,by decide⟩).lower ∧ (cell12856 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12856 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12856 ⟨45,by decide⟩).lower ∧ (cell12856 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12856 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12856 ⟨46,by decide⟩).lower ∧ (cell12856 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12856 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12856 ⟨47,by decide⟩).lower ∧ (cell12856 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12856 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12856 ⟨48,by decide⟩).lower ∧ (cell12856 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12856 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12856 ⟨49,by decide⟩).lower ∧ (cell12856 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12856 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12856 ⟨50,by decide⟩).lower ∧ (cell12856 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12856 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12856 ⟨51,by decide⟩).lower ∧ (cell12856 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12856 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12856 ⟨52,by decide⟩).lower ∧ (cell12856 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12856 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12856 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12856 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12856,cell12856,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12856 i).lower ∧
    (cell12856 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12856 i).upper ≤ (0.532 : ℝ) ∧
    (cell12856 i).centre ≤ (0.1 : ℝ) ∧ (cell12856 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12856 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12856 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12856

/-! The local source numeric instances at 12856 have no network premises. -/
namespace BstLean.Part269.N12856
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12856)
open BstLean.Part268 (cell12856)

noncomputable def sourceNumerics12856 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12856 (cell12856 i)
      scalarRow12856.M scalarRow12856.H scalarRow12856.xi := by
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
    energy_allowance := scalarRow12856.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12856]
    centre_nonneg := (scalarRow12856.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12856])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12856
/-! Actual 12857 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12857 ≤ (1.035587994699 : ℝ) := by
  have hr : (113.388711960229 : ℝ) ≤ √(12857 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.388711960229 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12857 12857 (11 / 1000) ≤
    (0.008430177640 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12857) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.388711960229 : ℝ) ≤ √(12857 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12857)
  have hdiv : K / √(12857 : ℝ) ≤ K / 113.388711960229 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.388711960229 ≤ (0.008430177640 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12857.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12857 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12857 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12857 := gPlus_lower 12857
end BstLean.Part269.N12857

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12857
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035587994698 : ℝ) ≤ wn 12857 := by
  have hn : √(12857 : ℝ) ≤ 113.388711960230 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12857 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.388711960230 ≤ 2 / √(12857 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248751950 : ℝ) ≤ rhoBar 12857 BstLean.Part154.csC ∧
    rhoBar 12857 BstLean.Part154.csC ≤ 0.000248752335 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035587994698 : ℝ) / (1.295212 * 12857) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035587994699 : ℝ) / (1.29521 * 12857) := by gcongr
      _ ≤ (0.000248752335 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12857 BstLean.Part154.csC) ≤ 0.000995071218 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12857 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) ≤ 0.000189998602 ∧
    cc1 (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) ≤ 0.000120897395 ∧
    cc2 (rhoBar 12857 BstLean.Part154.csC) ≤ 0.000070181891 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12857 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12857 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12857 BstLean.Part154.csC * nuR (rhoBar 12857 BstLean.Part154.csC)) ≤ 0.000497520140 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248752335 : ℝ) * 0.000995071218 := by gcongr
      _ ≤ (0.000497520140 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12857 BstLean.Part154.csC) * nuR (rhoBar 12857 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000995071218 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12857 BstLean.Part154.csC) * rhoBar 12857 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248752335 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248752335 / 2 + 0.399 * 0.000995071218 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189998602 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497520140 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120897395 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248752335 / 1.414213562 := by gcongr
      _ ≤ (0.000070181891 : ℝ) := by norm_num

end BstLean.Part269.N12857

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12857
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) ≤ 1.55897E-7 := by
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12857 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12857 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12857 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189998602 : ℝ) ^ 2 + 0.000120897395 ^ 2 + 3 * 0.000070181891 ^ 2 +
        2 * 0.797885 * 0.000189998602 * 0.000120897395 + 2 * 0.000189998602 * 0.000070181891 +
        4 * 0.797885 * 0.000120897395 * 0.000070181891 := by gcongr
    _ ≤ (1.55897E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12857 BstLean.Part154.csC Θ ≤ 0.002596081143 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12857 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12857 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12857 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035587994699 * 1.55897E-7 / (0.000248751950 : ℝ) := by gcongr
    _ ≤ 0.002596081143 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12857 BstLean.Part154.csC Θ ≤ 0.002879865398 + 0.000655985709 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12857 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12857 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035587994699 : ℝ) * ((2 * Θ * 0.000248752335 +
        (6863 / 10000) * 0.000248752335 * 12857 * 0.000995071218) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002879865398 + 0.000655985709 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12857 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12857 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12857 0.011 Θ ∧ gammaRatio 12857 0.011 Θ ≤ 0.000085514621 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12857 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035587994699 : ℝ) * 0.525 / ((1 - 0.011) * 12857) := by gcongr
      _ ≤ (0.000085514621 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12857 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12857 0.011 Θ) :=
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
    badAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12857 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12857 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12857 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12857 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12857 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12857 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12857 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12857 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12857 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12857 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035587994699 : ℝ) * 12857 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003362608560 + 0.003252066852 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12857

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12857
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12857 BstLean.Part154.csC) (piBar (rhoBar 12857 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12857 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12857 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12857 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12857 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12857 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12857 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12857 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12857 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12857 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12857 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052159414948 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12857) ≤ 0.010532243999 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12857 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035587994699)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010532243999 + 2 * 0.737676 / 12857) := by gcongr
    _ ≤ (0.052159414948 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12857 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12857

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12857
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510581597 : ℝ) ≤ plow 12857 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12857) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576543658)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362942601) : eMP 12857 0.011 xi bn ≤ 0.001173571749 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12857 : ℝ) * (1 - 0.011))) ≤ 0.000580290921 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362942601 / (12857 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580290921 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580290921 : ℝ) + 3.141593 * 0.052576543658 / (12857 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173571749 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576543658)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362942601) : PiBarMP 12857 12 0.011 xi bn ≤ 0.160253533358 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12857 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036918052509 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.763349542304 : ℝ) ≤ √((12857 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.388711960229 : ℝ) ≤ √(12857 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12857) ≤ 0.122872974055 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036918052509 + 0.052576543658 * 1.772454 / (2 * (112.763349542304 : ℝ))) * (1 + 0.001173571749) +
        8 / (12857 * 113.388711960229) + 0.122872974055 := by gcongr
    _ ≤ (0.160253533358 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576543658)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362942601) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281455170814) :
    parallelOracle 12857 0.011 xi bn cd ≤ 0.161231584481 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12857 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12857 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510581597 : ℝ) ≤ plow 12857 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.388711960229 : ℝ) ≤ √(12857 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281455170814 : ℝ) / (2 * 0.560510581597 * 113.388711960229)) * 0.160253533358 +
        0.281455170814 ^ 2 / (2 * 0.560510581597 * 113.388711960229) := by gcongr
    _ ≤ (0.161231584481 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576543658) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362942601)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281455170814) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12857 12857 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510581597 : ℝ) ≤ plow 12857 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.388711960229 : ℝ) ≤ √(12857 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12857 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12857 Θ 1.22 ≤ 0.011695172095 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.388711960229 := by gcongr <;> linarith
      _ ≤ (0.011695172095 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12857 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12857 12857 0.011 ≤ 0.008430177640 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12857 12857 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12857 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12857 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12857 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12857 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161231584481 + 0.011695172095 + (0.008430177640 : ℝ) *
        (1 + 2 * (0.281455170814 + 0.011695172095) / (0.560510581597 * 113.388711960229))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12857]

end BstLean.Part269.N12857

/-! The original eight local profiles supply actual 12857 moment certificates. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12857 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052576543658 ∧
    0 ≤ bN 12857 BstLean.Part154.csC (groupTheta g) ∧ bN 12857 BstLean.Part154.csC (groupTheta g) ≤ 0.001362942601 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12857 12857 0.011
      (momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12857 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12857 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12857 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229295755866 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12857 0.011
      (momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12857 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12857
/-! The actual computed-centre upper energy formula at 12857. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12857

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12857)
open BstLean.Part268 (cell12857)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085045083288
  | 2 => 0.085979933708
  | 3 => 0.086911817251
  | 4 => 0.087841893980
  | 5 => 0.088771575045
  | 6 => 0.089702560993
  | 7 => 0.090636883869
  | 8 => 0.091576953186
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12857 12857 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12857 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12857

/-! Actual upper energy certificates on all 43 source endpoints at 12857. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12857)
open BstLean.Part268 (cell12857)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12857 (gMinus 12857) (1 - (cell12857 i).lower) ≤ 1 ∧
    energyUpper 12857 (gMinus 12857) (BstLean.Part211.gPlus 12857)
      (finiteEnergy 12857 12857 0.011) (1 - (cell12857 i).lower) ≤
      (cell12857 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨10,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨11,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨12,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨13,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨14,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨15,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨16,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨17,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨18,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨19,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨20,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨21,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨22,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨23,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨24,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨25,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨26,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨27,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨28,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨29,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨30,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨31,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨32,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨33,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨34,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨35,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨36,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨37,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨38,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨39,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨40,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨41,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨42,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨43,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨44,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨45,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨46,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨47,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨48,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨49,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨50,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨51,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12857) (by norm_num)
        (q := 1 - (cell12857 ⟨52,by decide⟩).lower)
        (by norm_num [cell12857]) (by norm_num [cell12857])
      exact ⟨E.1,E.2.trans (by norm_num [cell12857])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12857

/-! Source-cell containment and simple scalar guards at 12857. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12857)
open BstLean.Part268 (cell12857)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12857 ⟨10,by decide⟩).lower ∧ (cell12857 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12857 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12857 ⟨11,by decide⟩).lower ∧ (cell12857 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12857 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12857 ⟨12,by decide⟩).lower ∧ (cell12857 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12857 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12857 ⟨13,by decide⟩).lower ∧ (cell12857 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12857 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12857 ⟨14,by decide⟩).lower ∧ (cell12857 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12857 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12857 ⟨15,by decide⟩).lower ∧ (cell12857 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12857 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12857 ⟨16,by decide⟩).lower ∧ (cell12857 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12857 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12857 ⟨17,by decide⟩).lower ∧ (cell12857 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12857 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12857 ⟨18,by decide⟩).lower ∧ (cell12857 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12857 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12857 ⟨19,by decide⟩).lower ∧ (cell12857 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12857 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12857 ⟨20,by decide⟩).lower ∧ (cell12857 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12857 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12857 ⟨21,by decide⟩).lower ∧ (cell12857 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12857 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12857 ⟨22,by decide⟩).lower ∧ (cell12857 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12857 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12857 ⟨23,by decide⟩).lower ∧ (cell12857 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12857 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12857 ⟨24,by decide⟩).lower ∧ (cell12857 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12857 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12857 ⟨25,by decide⟩).lower ∧ (cell12857 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12857 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12857 ⟨26,by decide⟩).lower ∧ (cell12857 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12857 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12857 ⟨27,by decide⟩).lower ∧ (cell12857 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12857 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12857 ⟨28,by decide⟩).lower ∧ (cell12857 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12857 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12857 ⟨29,by decide⟩).lower ∧ (cell12857 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12857 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12857 ⟨30,by decide⟩).lower ∧ (cell12857 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12857 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12857 ⟨31,by decide⟩).lower ∧ (cell12857 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12857 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12857 ⟨32,by decide⟩).lower ∧ (cell12857 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12857 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12857 ⟨33,by decide⟩).lower ∧ (cell12857 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12857 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12857 ⟨34,by decide⟩).lower ∧ (cell12857 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12857 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12857 ⟨35,by decide⟩).lower ∧ (cell12857 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12857 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12857 ⟨36,by decide⟩).lower ∧ (cell12857 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12857 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12857 ⟨37,by decide⟩).lower ∧ (cell12857 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12857 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12857 ⟨38,by decide⟩).lower ∧ (cell12857 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12857 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12857 ⟨39,by decide⟩).lower ∧ (cell12857 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12857 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12857 ⟨40,by decide⟩).lower ∧ (cell12857 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12857 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12857 ⟨41,by decide⟩).lower ∧ (cell12857 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12857 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12857 ⟨42,by decide⟩).lower ∧ (cell12857 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12857 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12857 ⟨43,by decide⟩).lower ∧ (cell12857 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12857 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12857 ⟨44,by decide⟩).lower ∧ (cell12857 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12857 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12857 ⟨45,by decide⟩).lower ∧ (cell12857 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12857 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12857 ⟨46,by decide⟩).lower ∧ (cell12857 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12857 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12857 ⟨47,by decide⟩).lower ∧ (cell12857 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12857 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12857 ⟨48,by decide⟩).lower ∧ (cell12857 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12857 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12857 ⟨49,by decide⟩).lower ∧ (cell12857 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12857 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12857 ⟨50,by decide⟩).lower ∧ (cell12857 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12857 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12857 ⟨51,by decide⟩).lower ∧ (cell12857 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12857 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12857 ⟨52,by decide⟩).lower ∧ (cell12857 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12857 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12857 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12857 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12857,cell12857,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12857 i).lower ∧
    (cell12857 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12857 i).upper ≤ (0.532 : ℝ) ∧
    (cell12857 i).centre ≤ (0.1 : ℝ) ∧ (cell12857 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12857 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12857 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12857

/-! The local source numeric instances at 12857 have no network premises. -/
namespace BstLean.Part269.N12857
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12857)
open BstLean.Part268 (cell12857)

noncomputable def sourceNumerics12857 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12857 (cell12857 i)
      scalarRow12857.M scalarRow12857.H scalarRow12857.xi := by
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
    energy_allowance := scalarRow12857.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12857]
    centre_nonneg := (scalarRow12857.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12857])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12857
/-! Actual 12858 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12858 ≤ (1.035586598689 : ℝ) := by
  have hr : (113.393121484506 : ℝ) ≤ √(12858 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.393121484506 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12858 12858 (11 / 1000) ≤
    (0.008429849813 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12858) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.393121484506 : ℝ) ≤ √(12858 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12858)
  have hdiv : K / √(12858 : ℝ) ≤ K / 113.393121484506 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.393121484506 ≤ (0.008429849813 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12858.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12858 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12858 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12858 := gPlus_lower 12858
end BstLean.Part269.N12858

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12858
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035586598688 : ℝ) ≤ wn 12858 := by
  have hn : √(12858 : ℝ) ≤ 113.393121484507 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12858 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.393121484507 ≤ 2 / √(12858 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248732269 : ℝ) ≤ rhoBar 12858 BstLean.Part154.csC ∧
    rhoBar 12858 BstLean.Part154.csC ≤ 0.000248732654 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035586598688 : ℝ) / (1.295212 * 12858) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035586598689 : ℝ) / (1.29521 * 12858) := by gcongr
      _ ≤ (0.000248732654 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12858 BstLean.Part154.csC) ≤ 0.000994992484 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12858 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) ≤ 0.000189983569 ∧
    cc1 (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) ≤ 0.000120887829 ∧
    cc2 (rhoBar 12858 BstLean.Part154.csC) ≤ 0.000070176339 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12858 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12858 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12858 BstLean.Part154.csC * nuR (rhoBar 12858 BstLean.Part154.csC)) ≤ 0.000497480775 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248732654 : ℝ) * 0.000994992484 := by gcongr
      _ ≤ (0.000497480775 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12858 BstLean.Part154.csC) * nuR (rhoBar 12858 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994992484 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12858 BstLean.Part154.csC) * rhoBar 12858 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248732654 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248732654 / 2 + 0.399 * 0.000994992484 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189983569 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497480775 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120887829 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248732654 / 1.414213562 := by gcongr
      _ ≤ (0.000070176339 : ℝ) := by norm_num

end BstLean.Part269.N12858

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12858
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) ≤ 1.55872E-7 := by
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12858 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12858 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12858 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189983569 : ℝ) ^ 2 + 0.000120887829 ^ 2 + 3 * 0.000070176339 ^ 2 +
        2 * 0.797885 * 0.000189983569 * 0.000120887829 + 2 * 0.000189983569 * 0.000070176339 +
        4 * 0.797885 * 0.000120887829 * 0.000070176339 := by gcongr
    _ ≤ (1.55872E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12858 BstLean.Part154.csC Θ ≤ 0.002595866712 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12858 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12858 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12858 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035586598689 * 1.55872E-7 / (0.000248732269 : ℝ) := by gcongr
    _ ≤ 0.002595866712 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12858 BstLean.Part154.csC Θ ≤ 0.002879629772 + 0.000655932924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12858 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12858 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035586598689 : ℝ) * ((2 * Θ * 0.000248732654 +
        (6863 / 10000) * 0.000248732654 * 12858 * 0.000994992484) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002879629772 + 0.000655932924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12858 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12858 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12858 0.011 Θ ∧ gammaRatio 12858 0.011 Θ ≤ 0.000085507855 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12858 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035586598689 : ℝ) * 0.525 / ((1 - 0.011) * 12858) := by gcongr
      _ ≤ (0.000085507855 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12858 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12858 0.011 Θ) :=
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
    badAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12858 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12858 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12858 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12858 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12858 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12858 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12858 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12858 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12858 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12858 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035586598689 : ℝ) * 12858 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003362372934 + 0.003251799636 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12858

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12858
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12858 BstLean.Part154.csC) (piBar (rhoBar 12858 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12858 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12858 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12858 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12858 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12858 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12858 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12858 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12858 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12858 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12858 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052157364762 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12858) ≤ 0.010531834431 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12858 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035586598689)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010531834431 + 2 * 0.737676 / 12858) := by gcongr
    _ ≤ (0.052157364762 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12858 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12858

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12858
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510625719 : ℝ) ≤ plow 12858 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12858) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576167743)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362830024) : eMP 12858 0.011 xi bn ≤ 0.001173477584 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12858 : ℝ) * (1 - 0.011))) ≤ 0.000580244390 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362830024 / (12858 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580244390 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580244390 : ℝ) + 3.141593 * 0.052576167743 / (12858 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173477584 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576167743)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362830024) : PiBarMP 12858 12 0.011 xi bn ≤ 0.160247205482 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12858 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036916527790 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.767734747134 : ℝ) ≤ √((12858 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.393121484506 : ℝ) ≤ √(12858 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12858) ≤ 0.122868195887 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036916527790 + 0.052576167743 * 1.772454 / (2 * (112.767734747134 : ℝ))) * (1 + 0.001173477584) +
        8 / (12858 * 113.393121484506) + 0.122868195887 := by gcongr
    _ ≤ (0.160247205482 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576167743)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362830024) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281452300910) :
    parallelOracle 12858 0.011 xi bn cd ≤ 0.161225188157 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12858 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12858 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510625719 : ℝ) ≤ plow 12858 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.393121484506 : ℝ) ≤ √(12858 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281452300910 : ℝ) / (2 * 0.560510625719 * 113.393121484506)) * 0.160247205482 +
        0.281452300910 ^ 2 / (2 * 0.560510625719 * 113.393121484506) := by gcongr
    _ ≤ (0.161225188157 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052576167743) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362830024)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281452300910) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12858 12858 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510625719 : ℝ) ≤ plow 12858 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.393121484506 : ℝ) ≤ √(12858 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12858 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12858 Θ 1.22 ≤ 0.011694717305 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.393121484506 := by gcongr <;> linarith
      _ ≤ (0.011694717305 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12858 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12858 12858 0.011 ≤ 0.008429849813 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12858 12858 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12858 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12858 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12858 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12858 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161225188157 + 0.011694717305 + (0.008429849813 : ℝ) *
        (1 + 2 * (0.281452300910 + 0.011694717305) / (0.560510625719 * 113.393121484506))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12858]

end BstLean.Part269.N12858

/-! The original eight local profiles supply actual 12858 moment certificates. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12858 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052576167743 ∧
    0 ≤ bN 12858 BstLean.Part154.csC (groupTheta g) ∧ bN 12858 BstLean.Part154.csC (groupTheta g) ≤ 0.001362830024 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12858 12858 0.011
      (momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12858 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12858 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12858 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229294936148 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12858 0.011
      (momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12858 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12858
/-! The actual computed-centre upper energy formula at 12858. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12858

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12858)
open BstLean.Part268 (cell12858)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085042324972
  | 2 => 0.085977128154
  | 3 => 0.086908958132
  | 4 => 0.087838973478
  | 5 => 0.088768583576
  | 6 => 0.089699486904
  | 7 => 0.090633713094
  | 8 => 0.091573668870
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12858 12858 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12858 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12858

/-! Actual upper energy certificates on all 43 source endpoints at 12858. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12858)
open BstLean.Part268 (cell12858)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12858 (gMinus 12858) (1 - (cell12858 i).lower) ≤ 1 ∧
    energyUpper 12858 (gMinus 12858) (BstLean.Part211.gPlus 12858)
      (finiteEnergy 12858 12858 0.011) (1 - (cell12858 i).lower) ≤
      (cell12858 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨10,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨11,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨12,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨13,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨14,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨15,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨16,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨17,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨18,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨19,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨20,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨21,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨22,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨23,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨24,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨25,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨26,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨27,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨28,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨29,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨30,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨31,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨32,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨33,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨34,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨35,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨36,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨37,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨38,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨39,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨40,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨41,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨42,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨43,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨44,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨45,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨46,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨47,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨48,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨49,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨50,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨51,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12858) (by norm_num)
        (q := 1 - (cell12858 ⟨52,by decide⟩).lower)
        (by norm_num [cell12858]) (by norm_num [cell12858])
      exact ⟨E.1,E.2.trans (by norm_num [cell12858])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12858

/-! Source-cell containment and simple scalar guards at 12858. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12858)
open BstLean.Part268 (cell12858)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12858 ⟨10,by decide⟩).lower ∧ (cell12858 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12858 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12858 ⟨11,by decide⟩).lower ∧ (cell12858 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12858 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12858 ⟨12,by decide⟩).lower ∧ (cell12858 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12858 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12858 ⟨13,by decide⟩).lower ∧ (cell12858 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12858 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12858 ⟨14,by decide⟩).lower ∧ (cell12858 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12858 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12858 ⟨15,by decide⟩).lower ∧ (cell12858 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12858 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12858 ⟨16,by decide⟩).lower ∧ (cell12858 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12858 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12858 ⟨17,by decide⟩).lower ∧ (cell12858 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12858 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12858 ⟨18,by decide⟩).lower ∧ (cell12858 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12858 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12858 ⟨19,by decide⟩).lower ∧ (cell12858 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12858 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12858 ⟨20,by decide⟩).lower ∧ (cell12858 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12858 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12858 ⟨21,by decide⟩).lower ∧ (cell12858 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12858 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12858 ⟨22,by decide⟩).lower ∧ (cell12858 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12858 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12858 ⟨23,by decide⟩).lower ∧ (cell12858 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12858 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12858 ⟨24,by decide⟩).lower ∧ (cell12858 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12858 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12858 ⟨25,by decide⟩).lower ∧ (cell12858 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12858 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12858 ⟨26,by decide⟩).lower ∧ (cell12858 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12858 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12858 ⟨27,by decide⟩).lower ∧ (cell12858 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12858 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12858 ⟨28,by decide⟩).lower ∧ (cell12858 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12858 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12858 ⟨29,by decide⟩).lower ∧ (cell12858 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12858 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12858 ⟨30,by decide⟩).lower ∧ (cell12858 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12858 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12858 ⟨31,by decide⟩).lower ∧ (cell12858 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12858 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12858 ⟨32,by decide⟩).lower ∧ (cell12858 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12858 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12858 ⟨33,by decide⟩).lower ∧ (cell12858 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12858 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12858 ⟨34,by decide⟩).lower ∧ (cell12858 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12858 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12858 ⟨35,by decide⟩).lower ∧ (cell12858 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12858 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12858 ⟨36,by decide⟩).lower ∧ (cell12858 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12858 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12858 ⟨37,by decide⟩).lower ∧ (cell12858 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12858 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12858 ⟨38,by decide⟩).lower ∧ (cell12858 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12858 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12858 ⟨39,by decide⟩).lower ∧ (cell12858 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12858 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12858 ⟨40,by decide⟩).lower ∧ (cell12858 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12858 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12858 ⟨41,by decide⟩).lower ∧ (cell12858 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12858 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12858 ⟨42,by decide⟩).lower ∧ (cell12858 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12858 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12858 ⟨43,by decide⟩).lower ∧ (cell12858 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12858 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12858 ⟨44,by decide⟩).lower ∧ (cell12858 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12858 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12858 ⟨45,by decide⟩).lower ∧ (cell12858 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12858 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12858 ⟨46,by decide⟩).lower ∧ (cell12858 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12858 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12858 ⟨47,by decide⟩).lower ∧ (cell12858 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12858 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12858 ⟨48,by decide⟩).lower ∧ (cell12858 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12858 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12858 ⟨49,by decide⟩).lower ∧ (cell12858 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12858 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12858 ⟨50,by decide⟩).lower ∧ (cell12858 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12858 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12858 ⟨51,by decide⟩).lower ∧ (cell12858 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12858 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12858 ⟨52,by decide⟩).lower ∧ (cell12858 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12858 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12858 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12858 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12858,cell12858,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12858 i).lower ∧
    (cell12858 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12858 i).upper ≤ (0.532 : ℝ) ∧
    (cell12858 i).centre ≤ (0.1 : ℝ) ∧ (cell12858 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12858 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12858 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12858

/-! The local source numeric instances at 12858 have no network premises. -/
namespace BstLean.Part269.N12858
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12858)
open BstLean.Part268 (cell12858)

noncomputable def sourceNumerics12858 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12858 (cell12858 i)
      scalarRow12858.M scalarRow12858.H scalarRow12858.xi := by
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
    energy_allowance := scalarRow12858.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12858]
    centre_nonneg := (scalarRow12858.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12858])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12858
/-! Actual 12859 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12859 ≤ (1.035585202843 : ℝ) := by
  have hr : (113.397530837315 : ℝ) ≤ √(12859 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.397530837315 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12859 12859 (11 / 1000) ≤
    (0.008429522024 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12859) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.397530837315 : ℝ) ≤ √(12859 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12859)
  have hdiv : K / √(12859 : ℝ) ≤ K / 113.397530837315 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.397530837315 ≤ (0.008429522024 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12859.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12859 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12859 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12859 := gPlus_lower 12859
end BstLean.Part269.N12859

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12859
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035585202842 : ℝ) ≤ wn 12859 := by
  have hn : √(12859 : ℝ) ≤ 113.397530837316 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12859 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.397530837316 ≤ 2 / √(12859 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248712591 : ℝ) ≤ rhoBar 12859 BstLean.Part154.csC ∧
    rhoBar 12859 BstLean.Part154.csC ≤ 0.000248712976 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035585202842 : ℝ) / (1.295212 * 12859) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035585202843 : ℝ) / (1.29521 * 12859) := by gcongr
      _ ≤ (0.000248712976 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12859 BstLean.Part154.csC) ≤ 0.000994913763 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12859 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) ≤ 0.000189968538 ∧
    cc1 (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) ≤ 0.000120878265 ∧
    cc2 (rhoBar 12859 BstLean.Part154.csC) ≤ 0.000070170787 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12859 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12859 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12859 BstLean.Part154.csC * nuR (rhoBar 12859 BstLean.Part154.csC)) ≤ 0.000497441417 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248712976 : ℝ) * 0.000994913763 := by gcongr
      _ ≤ (0.000497441417 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12859 BstLean.Part154.csC) * nuR (rhoBar 12859 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994913763 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12859 BstLean.Part154.csC) * rhoBar 12859 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248712976 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248712976 / 2 + 0.399 * 0.000994913763 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189968538 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497441417 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120878265 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248712976 / 1.414213562 := by gcongr
      _ ≤ (0.000070170787 : ℝ) := by norm_num

end BstLean.Part269.N12859

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12859
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) ≤ 1.55847E-7 := by
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12859 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12859 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12859 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189968538 : ℝ) ^ 2 + 0.000120878265 ^ 2 + 3 * 0.000070170787 ^ 2 +
        2 * 0.797885 * 0.000189968538 * 0.000120878265 + 2 * 0.000189968538 * 0.000070170787 +
        4 * 0.797885 * 0.000120878265 * 0.000070170787 := by gcongr
    _ ≤ (1.55847E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12859 BstLean.Part154.csC Θ ≤ 0.002595652218 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12859 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12859 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12859 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035585202843 * 1.55847E-7 / (0.000248712591 : ℝ) := by gcongr
    _ ≤ 0.002595652218 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12859 BstLean.Part154.csC Θ ≤ 0.002879394186 + 0.000655880147 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12859 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12859 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035585202843 : ℝ) * ((2 * Θ * 0.000248712976 +
        (6863 / 10000) * 0.000248712976 * 12859 * 0.000994913763) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002879394186 + 0.000655880147 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12859 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12859 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12859 0.011 Θ ∧ gammaRatio 12859 0.011 Θ ≤ 0.000085501090 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12859 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035585202843 : ℝ) * 0.525 / ((1 - 0.011) * 12859) := by gcongr
      _ ≤ (0.000085501090 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12859 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12859 0.011 Θ) :=
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
    badAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12859 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12859 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12859 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12859 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12859 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12859 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12859 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12859 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12859 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12859 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035585202843 : ℝ) * 12859 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003362137348 + 0.003251532365 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12859

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12859
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12859 BstLean.Part154.csC) (piBar (rhoBar 12859 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12859 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12859 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12859 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12859 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12859 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12859 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12859 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12859 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12859 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12859 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052155314818 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12859) ≤ 0.010531424911 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12859 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035585202843)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010531424911 + 2 * 0.737676 / 12859) := by gcongr
    _ ≤ (0.052155314818 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12859 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12859

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12859
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510669834 : ℝ) ≤ plow 12859 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12859) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575791840)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362717415) : eMP 12859 0.011 xi bn ≤ 0.001173383413 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12859 : ℝ) * (1 - 0.011))) ≤ 0.000580197856 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362717415 / (12859 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580197856 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580197856 : ℝ) + 3.141593 * 0.052575791840 / (12859 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173383413 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575791840)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362717415) : PiBarMP 12859 12 0.011 xi bn ≤ 0.160240877668 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12859 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036915002574 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.772119781442 : ℝ) ≤ √((12859 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.397530837315 : ℝ) ≤ √(12859 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12859) ≤ 0.122863418277 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036915002574 + 0.052575791840 * 1.772454 / (2 * (112.772119781442 : ℝ))) * (1 + 0.001173383413) +
        8 / (12859 * 113.397530837315) + 0.122863418277 := by gcongr
    _ ≤ (0.160240877668 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575791840)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362717415) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281449431272) :
    parallelOracle 12859 0.011 xi bn cd ≤ 0.161218791903 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12859 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12859 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510669834 : ℝ) ≤ plow 12859 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.397530837315 : ℝ) ≤ √(12859 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281449431272 : ℝ) / (2 * 0.560510669834 * 113.397530837315)) * 0.160240877668 +
        0.281449431272 ^ 2 / (2 * 0.560510669834 * 113.397530837315) := by gcongr
    _ ≤ (0.161218791903 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575791840) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362717415)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281449431272) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12859 12859 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510669834 : ℝ) ≤ plow 12859 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.397530837315 : ℝ) ≤ √(12859 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12859 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12859 Θ 1.22 ≤ 0.011694262567 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.397530837315 := by gcongr <;> linarith
      _ ≤ (0.011694262567 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12859 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12859 12859 0.011 ≤ 0.008429522024 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12859 12859 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12859 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12859 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12859 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12859 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161218791903 + 0.011694262567 + (0.008429522024 : ℝ) *
        (1 + 2 * (0.281449431272 + 0.011694262567) / (0.560510669834 * 113.397530837315))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12859]

end BstLean.Part269.N12859

/-! The original eight local profiles supply actual 12859 moment certificates. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12859 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052575791840 ∧
    0 ≤ bN 12859 BstLean.Part154.csC (groupTheta g) ∧ bN 12859 BstLean.Part154.csC (groupTheta g) ≤ 0.001362717415 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12859 12859 0.011
      (momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12859 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12859 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12859 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229294116454 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12859 0.011
      (momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12859 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12859
/-! The actual computed-centre upper energy formula at 12859. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12859

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12859)
open BstLean.Part268 (cell12859)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085039567584
  | 2 => 0.085974323562
  | 3 => 0.086906100022
  | 4 => 0.087836054039
  | 5 => 0.088765593238
  | 6 => 0.089696414027
  | 7 => 0.090630543632
  | 8 => 0.091570385985
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12859 12859 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12859 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12859

/-! Actual upper energy certificates on all 43 source endpoints at 12859. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12859)
open BstLean.Part268 (cell12859)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12859 (gMinus 12859) (1 - (cell12859 i).lower) ≤ 1 ∧
    energyUpper 12859 (gMinus 12859) (BstLean.Part211.gPlus 12859)
      (finiteEnergy 12859 12859 0.011) (1 - (cell12859 i).lower) ≤
      (cell12859 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨10,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨11,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨12,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨13,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨14,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨15,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨16,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨17,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨18,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨19,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨20,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨21,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨22,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨23,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨24,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨25,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨26,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨27,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨28,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨29,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨30,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨31,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨32,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨33,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨34,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨35,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨36,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨37,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨38,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨39,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨40,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨41,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨42,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨43,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨44,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨45,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨46,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨47,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨48,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨49,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨50,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨51,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12859) (by norm_num)
        (q := 1 - (cell12859 ⟨52,by decide⟩).lower)
        (by norm_num [cell12859]) (by norm_num [cell12859])
      exact ⟨E.1,E.2.trans (by norm_num [cell12859])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12859

/-! Source-cell containment and simple scalar guards at 12859. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12859)
open BstLean.Part268 (cell12859)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12859 ⟨10,by decide⟩).lower ∧ (cell12859 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12859 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12859 ⟨11,by decide⟩).lower ∧ (cell12859 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12859 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12859 ⟨12,by decide⟩).lower ∧ (cell12859 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12859 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12859 ⟨13,by decide⟩).lower ∧ (cell12859 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12859 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12859 ⟨14,by decide⟩).lower ∧ (cell12859 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12859 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12859 ⟨15,by decide⟩).lower ∧ (cell12859 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12859 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12859 ⟨16,by decide⟩).lower ∧ (cell12859 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12859 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12859 ⟨17,by decide⟩).lower ∧ (cell12859 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12859 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12859 ⟨18,by decide⟩).lower ∧ (cell12859 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12859 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12859 ⟨19,by decide⟩).lower ∧ (cell12859 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12859 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12859 ⟨20,by decide⟩).lower ∧ (cell12859 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12859 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12859 ⟨21,by decide⟩).lower ∧ (cell12859 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12859 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12859 ⟨22,by decide⟩).lower ∧ (cell12859 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12859 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12859 ⟨23,by decide⟩).lower ∧ (cell12859 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12859 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12859 ⟨24,by decide⟩).lower ∧ (cell12859 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12859 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12859 ⟨25,by decide⟩).lower ∧ (cell12859 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12859 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12859 ⟨26,by decide⟩).lower ∧ (cell12859 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12859 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12859 ⟨27,by decide⟩).lower ∧ (cell12859 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12859 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12859 ⟨28,by decide⟩).lower ∧ (cell12859 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12859 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12859 ⟨29,by decide⟩).lower ∧ (cell12859 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12859 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12859 ⟨30,by decide⟩).lower ∧ (cell12859 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12859 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12859 ⟨31,by decide⟩).lower ∧ (cell12859 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12859 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12859 ⟨32,by decide⟩).lower ∧ (cell12859 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12859 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12859 ⟨33,by decide⟩).lower ∧ (cell12859 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12859 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12859 ⟨34,by decide⟩).lower ∧ (cell12859 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12859 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12859 ⟨35,by decide⟩).lower ∧ (cell12859 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12859 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12859 ⟨36,by decide⟩).lower ∧ (cell12859 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12859 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12859 ⟨37,by decide⟩).lower ∧ (cell12859 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12859 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12859 ⟨38,by decide⟩).lower ∧ (cell12859 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12859 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12859 ⟨39,by decide⟩).lower ∧ (cell12859 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12859 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12859 ⟨40,by decide⟩).lower ∧ (cell12859 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12859 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12859 ⟨41,by decide⟩).lower ∧ (cell12859 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12859 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12859 ⟨42,by decide⟩).lower ∧ (cell12859 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12859 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12859 ⟨43,by decide⟩).lower ∧ (cell12859 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12859 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12859 ⟨44,by decide⟩).lower ∧ (cell12859 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12859 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12859 ⟨45,by decide⟩).lower ∧ (cell12859 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12859 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12859 ⟨46,by decide⟩).lower ∧ (cell12859 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12859 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12859 ⟨47,by decide⟩).lower ∧ (cell12859 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12859 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12859 ⟨48,by decide⟩).lower ∧ (cell12859 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12859 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12859 ⟨49,by decide⟩).lower ∧ (cell12859 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12859 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12859 ⟨50,by decide⟩).lower ∧ (cell12859 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12859 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12859 ⟨51,by decide⟩).lower ∧ (cell12859 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12859 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12859 ⟨52,by decide⟩).lower ∧ (cell12859 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12859 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12859 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12859 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12859,cell12859,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12859 i).lower ∧
    (cell12859 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12859 i).upper ≤ (0.532 : ℝ) ∧
    (cell12859 i).centre ≤ (0.1 : ℝ) ∧ (cell12859 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12859 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12859 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12859

/-! The local source numeric instances at 12859 have no network premises. -/
namespace BstLean.Part269.N12859
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12859)
open BstLean.Part268 (cell12859)

noncomputable def sourceNumerics12859 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12859 (cell12859 i)
      scalarRow12859.M scalarRow12859.H scalarRow12859.xi := by
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
    energy_allowance := scalarRow12859.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12859]
    centre_nonneg := (scalarRow12859.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12859])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12859
/-! Actual 12860 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12860 ≤ (1.035583807160 : ℝ) := by
  have hr : (113.401940018678 : ℝ) ≤ √(12860 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.401940018678 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12860 12860 (11 / 1000) ≤
    (0.008429194273 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12860) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.401940018678 : ℝ) ≤ √(12860 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12860)
  have hdiv : K / √(12860 : ℝ) ≤ K / 113.401940018678 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.401940018678 ≤ (0.008429194273 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12860.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12860 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12860 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12860 := gPlus_lower 12860
end BstLean.Part269.N12860

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12860
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035583807159 : ℝ) ≤ wn 12860 := by
  have hn : √(12860 : ℝ) ≤ 113.401940018679 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12860 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.401940018679 ≤ 2 / √(12860 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248692915 : ℝ) ≤ rhoBar 12860 BstLean.Part154.csC ∧
    rhoBar 12860 BstLean.Part154.csC ≤ 0.000248693300 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035583807159 : ℝ) / (1.295212 * 12860) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035583807160 : ℝ) / (1.29521 * 12860) := by gcongr
      _ ≤ (0.000248693300 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12860 BstLean.Part154.csC) ≤ 0.000994835049 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12860 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) ≤ 0.000189953508 ∧
    cc1 (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) ≤ 0.000120868702 ∧
    cc2 (rhoBar 12860 BstLean.Part154.csC) ≤ 0.000070165235 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12860 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12860 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12860 BstLean.Part154.csC * nuR (rhoBar 12860 BstLean.Part154.csC)) ≤ 0.000497402063 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248693300 : ℝ) * 0.000994835049 := by gcongr
      _ ≤ (0.000497402063 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12860 BstLean.Part154.csC) * nuR (rhoBar 12860 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994835049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12860 BstLean.Part154.csC) * rhoBar 12860 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248693300 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248693300 / 2 + 0.399 * 0.000994835049 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189953508 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497402063 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120868702 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248693300 / 1.414213562 := by gcongr
      _ ≤ (0.000070165235 : ℝ) := by norm_num

end BstLean.Part269.N12860

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12860
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) ≤ 1.55823E-7 := by
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12860 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12860 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12860 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189953508 : ℝ) ^ 2 + 0.000120868702 ^ 2 + 3 * 0.000070165235 ^ 2 +
        2 * 0.797885 * 0.000189953508 * 0.000120868702 + 2 * 0.000189953508 * 0.000070165235 +
        4 * 0.797885 * 0.000120868702 * 0.000070165235 := by gcongr
    _ ≤ (1.55823E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12860 BstLean.Part154.csC Θ ≤ 0.002595454328 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12860 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12860 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12860 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035583807160 * 1.55823E-7 / (0.000248692915 : ℝ) := by gcongr
    _ ≤ 0.002595454328 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12860 BstLean.Part154.csC Θ ≤ 0.002879158609 + 0.000655827376 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12860 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12860 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035583807160 : ℝ) * ((2 * Θ * 0.000248693300 +
        (6863 / 10000) * 0.000248693300 * 12860 * 0.000994835049) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002879158609 + 0.000655827376 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12860 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12860 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12860 0.011 Θ ∧ gammaRatio 12860 0.011 Θ ≤ 0.000085494326 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12860 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035583807160 : ℝ) * 0.525 / ((1 - 0.011) * 12860) := by gcongr
      _ ≤ (0.000085494326 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12860 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12860 0.011 Θ) :=
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
    badAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12860 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12860 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12860 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12860 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12860 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12860 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12860 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12860 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12860 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12860 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035583807160 : ℝ) * 12860 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003361901771 + 0.003251281704 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12860

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12860
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12860 BstLean.Part154.csC) (piBar (rhoBar 12860 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12860 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12860 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12860 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12860 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12860 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12860 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12860 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12860 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12860 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12860 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052153265115 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12860) ≤ 0.010531015439 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12860 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035583807160)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010531015439 + 2 * 0.737676 / 12860) := by gcongr
    _ ≤ (0.052153265115 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12860 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12860

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12860
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510713942 : ℝ) ≤ plow 12860 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12860) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575424666)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362613523) : eMP 12860 0.011 xi bn ≤ 0.001173292962 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12860 : ℝ) * (1 - 0.011))) ≤ 0.000580153181 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362613523 / (12860 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580153181 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580153181 : ℝ) + 3.141593 * 0.052575424666 / (12860 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173292962 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575424666)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362613523) : PiBarMP 12860 12 0.011 xi bn ≤ 0.160234668770 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12860 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036913595369 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.776504645249 : ℝ) ≤ √((12860 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.401940018678 : ℝ) ≤ √(12860 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12860) ≤ 0.122858641224 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036913595369 + 0.052575424666 * 1.772454 / (2 * (112.776504645249 : ℝ))) * (1 + 0.001173292962) +
        8 / (12860 * 113.401940018678) + 0.122858641224 := by gcongr
    _ ≤ (0.160234668770 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575424666)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362613523) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281446580906) :
    parallelOracle 12860 0.011 xi bn cd ≤ 0.161212514946 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12860 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12860 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510713942 : ℝ) ≤ plow 12860 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.401940018678 : ℝ) ≤ √(12860 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281446580906 : ℝ) / (2 * 0.560510713942 * 113.401940018678)) * 0.160234668770 +
        0.281446580906 ^ 2 / (2 * 0.560510713942 * 113.401940018678) := by gcongr
    _ ≤ (0.161212514946 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575424666) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362613523)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281446580906) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12860 12860 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510713942 : ℝ) ≤ plow 12860 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.401940018678 : ℝ) ≤ √(12860 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12860 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12860 Θ 1.22 ≤ 0.011693807882 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.401940018678 := by gcongr <;> linarith
      _ ≤ (0.011693807882 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12860 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12860 12860 0.011 ≤ 0.008429194273 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12860 12860 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12860 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12860 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12860 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12860 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161212514946 + 0.011693807882 + (0.008429194273 : ℝ) *
        (1 + 2 * (0.281446580906 + 0.011693807882) / (0.560510713942 * 113.401940018678))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12860]

end BstLean.Part269.N12860

/-! The original eight local profiles supply actual 12860 moment certificates. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12860 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052575424666 ∧
    0 ≤ bN 12860 BstLean.Part154.csC (groupTheta g) ∧ bN 12860 BstLean.Part154.csC (groupTheta g) ≤ 0.001362613523 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12860 12860 0.011
      (momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12860 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12860 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12860 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229293315791 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12860 0.011
      (momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12860 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12860
/-! The actual computed-centre upper energy formula at 12860. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12860

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12860)
open BstLean.Part268 (cell12860)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085036811121
  | 2 => 0.085971519934
  | 3 => 0.086903242919
  | 4 => 0.087833135663
  | 5 => 0.088762604029
  | 6 => 0.089693342363
  | 7 => 0.090627375481
  | 8 => 0.091567104532
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12860 12860 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12860 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12860

/-! Actual upper energy certificates on all 43 source endpoints at 12860. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12860)
open BstLean.Part268 (cell12860)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12860 (gMinus 12860) (1 - (cell12860 i).lower) ≤ 1 ∧
    energyUpper 12860 (gMinus 12860) (BstLean.Part211.gPlus 12860)
      (finiteEnergy 12860 12860 0.011) (1 - (cell12860 i).lower) ≤
      (cell12860 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨10,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨11,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨12,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨13,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨14,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨15,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨16,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨17,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨18,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨19,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨20,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨21,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨22,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨23,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨24,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨25,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨26,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨27,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨28,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨29,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨30,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨31,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨32,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨33,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨34,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨35,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨36,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨37,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨38,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨39,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨40,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨41,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨42,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨43,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨44,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨45,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨46,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨47,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨48,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨49,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨50,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨51,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12860) (by norm_num)
        (q := 1 - (cell12860 ⟨52,by decide⟩).lower)
        (by norm_num [cell12860]) (by norm_num [cell12860])
      exact ⟨E.1,E.2.trans (by norm_num [cell12860])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12860

/-! Source-cell containment and simple scalar guards at 12860. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12860)
open BstLean.Part268 (cell12860)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12860 ⟨10,by decide⟩).lower ∧ (cell12860 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12860 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12860 ⟨11,by decide⟩).lower ∧ (cell12860 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12860 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12860 ⟨12,by decide⟩).lower ∧ (cell12860 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12860 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12860 ⟨13,by decide⟩).lower ∧ (cell12860 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12860 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12860 ⟨14,by decide⟩).lower ∧ (cell12860 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12860 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12860 ⟨15,by decide⟩).lower ∧ (cell12860 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12860 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12860 ⟨16,by decide⟩).lower ∧ (cell12860 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12860 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12860 ⟨17,by decide⟩).lower ∧ (cell12860 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12860 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12860 ⟨18,by decide⟩).lower ∧ (cell12860 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12860 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12860 ⟨19,by decide⟩).lower ∧ (cell12860 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12860 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12860 ⟨20,by decide⟩).lower ∧ (cell12860 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12860 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12860 ⟨21,by decide⟩).lower ∧ (cell12860 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12860 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12860 ⟨22,by decide⟩).lower ∧ (cell12860 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12860 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12860 ⟨23,by decide⟩).lower ∧ (cell12860 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12860 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12860 ⟨24,by decide⟩).lower ∧ (cell12860 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12860 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12860 ⟨25,by decide⟩).lower ∧ (cell12860 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12860 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12860 ⟨26,by decide⟩).lower ∧ (cell12860 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12860 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12860 ⟨27,by decide⟩).lower ∧ (cell12860 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12860 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12860 ⟨28,by decide⟩).lower ∧ (cell12860 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12860 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12860 ⟨29,by decide⟩).lower ∧ (cell12860 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12860 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12860 ⟨30,by decide⟩).lower ∧ (cell12860 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12860 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12860 ⟨31,by decide⟩).lower ∧ (cell12860 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12860 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12860 ⟨32,by decide⟩).lower ∧ (cell12860 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12860 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12860 ⟨33,by decide⟩).lower ∧ (cell12860 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12860 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12860 ⟨34,by decide⟩).lower ∧ (cell12860 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12860 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12860 ⟨35,by decide⟩).lower ∧ (cell12860 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12860 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12860 ⟨36,by decide⟩).lower ∧ (cell12860 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12860 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12860 ⟨37,by decide⟩).lower ∧ (cell12860 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12860 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12860 ⟨38,by decide⟩).lower ∧ (cell12860 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12860 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12860 ⟨39,by decide⟩).lower ∧ (cell12860 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12860 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12860 ⟨40,by decide⟩).lower ∧ (cell12860 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12860 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12860 ⟨41,by decide⟩).lower ∧ (cell12860 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12860 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12860 ⟨42,by decide⟩).lower ∧ (cell12860 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12860 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12860 ⟨43,by decide⟩).lower ∧ (cell12860 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12860 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12860 ⟨44,by decide⟩).lower ∧ (cell12860 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12860 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12860 ⟨45,by decide⟩).lower ∧ (cell12860 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12860 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12860 ⟨46,by decide⟩).lower ∧ (cell12860 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12860 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12860 ⟨47,by decide⟩).lower ∧ (cell12860 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12860 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12860 ⟨48,by decide⟩).lower ∧ (cell12860 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12860 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12860 ⟨49,by decide⟩).lower ∧ (cell12860 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12860 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12860 ⟨50,by decide⟩).lower ∧ (cell12860 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12860 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12860 ⟨51,by decide⟩).lower ∧ (cell12860 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12860 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12860 ⟨52,by decide⟩).lower ∧ (cell12860 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12860 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12860 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12860 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12860,cell12860,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12860 i).lower ∧
    (cell12860 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12860 i).upper ≤ (0.532 : ℝ) ∧
    (cell12860 i).centre ≤ (0.1 : ℝ) ∧ (cell12860 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12860 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12860 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12860

/-! The local source numeric instances at 12860 have no network premises. -/
namespace BstLean.Part269.N12860
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12860)
open BstLean.Part268 (cell12860)

noncomputable def sourceNumerics12860 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12860 (cell12860 i)
      scalarRow12860.M scalarRow12860.H scalarRow12860.xi := by
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
    energy_allowance := scalarRow12860.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12860]
    centre_nonneg := (scalarRow12860.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12860])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12860
/-! Actual 12861 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12861 ≤ (1.035582411641 : ℝ) := by
  have hr : (113.406349028614 : ℝ) ≤ √(12861 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.406349028614 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12861 12861 (11 / 1000) ≤
    (0.008428866561 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12861) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.406349028614 : ℝ) ≤ √(12861 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12861)
  have hdiv : K / √(12861 : ℝ) ≤ K / 113.406349028614 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.406349028614 ≤ (0.008428866561 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12861.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12861 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12861 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12861 := gPlus_lower 12861
end BstLean.Part269.N12861

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12861
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035582411640 : ℝ) ≤ wn 12861 := by
  have hn : √(12861 : ℝ) ≤ 113.406349028615 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12861 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.406349028615 ≤ 2 / √(12861 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248673243 : ℝ) ≤ rhoBar 12861 BstLean.Part154.csC ∧
    rhoBar 12861 BstLean.Part154.csC ≤ 0.000248673628 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035582411640 : ℝ) / (1.295212 * 12861) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035582411641 : ℝ) / (1.29521 * 12861) := by gcongr
      _ ≤ (0.000248673628 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12861 BstLean.Part154.csC) ≤ 0.000994756351 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12861 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) ≤ 0.000189938482 ∧
    cc1 (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) ≤ 0.000120859140 ∧
    cc2 (rhoBar 12861 BstLean.Part154.csC) ≤ 0.000070159685 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12861 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12861 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12861 BstLean.Part154.csC * nuR (rhoBar 12861 BstLean.Part154.csC)) ≤ 0.000497362716 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248673628 : ℝ) * 0.000994756351 := by gcongr
      _ ≤ (0.000497362716 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12861 BstLean.Part154.csC) * nuR (rhoBar 12861 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994756351 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12861 BstLean.Part154.csC) * rhoBar 12861 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248673628 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248673628 / 2 + 0.399 * 0.000994756351 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189938482 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497362716 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120859140 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248673628 / 1.414213562 := by gcongr
      _ ≤ (0.000070159685 : ℝ) := by norm_num

end BstLean.Part269.N12861

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12861
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) ≤ 1.55798E-7 := by
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12861 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12861 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12861 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189938482 : ℝ) ^ 2 + 0.000120859140 ^ 2 + 3 * 0.000070159685 ^ 2 +
        2 * 0.797885 * 0.000189938482 * 0.000120859140 + 2 * 0.000189938482 * 0.000070159685 +
        4 * 0.797885 * 0.000120859140 * 0.000070159685 := by gcongr
    _ ≤ (1.55798E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12861 BstLean.Part154.csC Θ ≤ 0.002595239707 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12861 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12861 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12861 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035582411641 * 1.55798E-7 / (0.000248673243 : ℝ) := by gcongr
    _ ≤ 0.002595239707 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12861 BstLean.Part154.csC Θ ≤ 0.002878923091 + 0.000655774615 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12861 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12861 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035582411641 : ℝ) * ((2 * Θ * 0.000248673628 +
        (6863 / 10000) * 0.000248673628 * 12861 * 0.000994756351) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002878923091 + 0.000655774615 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12861 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12861 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12861 0.011 Θ ∧ gammaRatio 12861 0.011 Θ ≤ 0.000085487563 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12861 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035582411641 : ℝ) * 0.525 / ((1 - 0.011) * 12861) := by gcongr
      _ ≤ (0.000085487563 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12861 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12861 0.011 Θ) :=
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
    badAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12861 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12861 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12861 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12861 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12861 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12861 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12861 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12861 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12861 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12861 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035582411641 : ℝ) * 12861 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003361666253 + 0.003251014322 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12861

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12861
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12861 BstLean.Part154.csC) (piBar (rhoBar 12861 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12861 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12861 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12861 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12861 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12861 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12861 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12861 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12861 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12861 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12861 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052151215650 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12861) ≤ 0.010530606014 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12861 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035582411641)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010530606014 + 2 * 0.737676 / 12861) := by gcongr
    _ ≤ (0.052151215650 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12861 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12861

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12861
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510758043 : ℝ) ≤ plow 12861 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12861) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575048773)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362500847) : eMP 12861 0.011 xi bn ≤ 0.001173198777 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12861 : ℝ) * (1 - 0.011))) ≤ 0.000580106640 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362500847 / (12861 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580106640 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580106640 : ℝ) + 3.141593 * 0.052575048773 / (12861 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173198777 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575048773)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362500847) : PiBarMP 12861 12 0.011 xi bn ≤ 0.160228341045 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12861 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036912069124 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.780889338575 : ℝ) ≤ √((12861 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.406349028614 : ℝ) ≤ √(12861 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12861) ≤ 0.122853864728 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036912069124 + 0.052575048773 * 1.772454 / (2 * (112.780889338575 : ℝ))) * (1 + 0.001173198777) +
        8 / (12861 * 113.406349028614) + 0.122853864728 := by gcongr
    _ ≤ (0.160228341045 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575048773)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362500847) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281443711762) :
    parallelOracle 12861 0.011 xi bn cd ≤ 0.161206118800 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12861 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12861 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510758043 : ℝ) ≤ plow 12861 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.406349028614 : ℝ) ≤ √(12861 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281443711762 : ℝ) / (2 * 0.560510758043 * 113.406349028614)) * 0.160228341045 +
        0.281443711762 ^ 2 / (2 * 0.560510758043 * 113.406349028614) := by gcongr
    _ ≤ (0.161206118800 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052575048773) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362500847)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281443711762) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12861 12861 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510758043 : ℝ) ≤ plow 12861 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.406349028614 : ℝ) ≤ √(12861 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12861 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12861 Θ 1.22 ≤ 0.011693353251 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.406349028614 := by gcongr <;> linarith
      _ ≤ (0.011693353251 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12861 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12861 12861 0.011 ≤ 0.008428866561 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12861 12861 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12861 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12861 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12861 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12861 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161206118800 + 0.011693353251 + (0.008428866561 : ℝ) *
        (1 + 2 * (0.281443711762 + 0.011693353251) / (0.560510758043 * 113.406349028614))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12861]

end BstLean.Part269.N12861

/-! The original eight local profiles supply actual 12861 moment certificates. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12861 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052575048773 ∧
    0 ≤ bN 12861 BstLean.Part154.csC (groupTheta g) ∧ bN 12861 BstLean.Part154.csC (groupTheta g) ≤ 0.001362500847 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12861 12861 0.011
      (momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12861 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12861 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12861 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229292496112 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12861 0.011
      (momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12861 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12861
/-! The actual computed-centre upper energy formula at 12861. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12861

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12861)
open BstLean.Part268 (cell12861)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085034055584
  | 2 => 0.085968717266
  | 3 => 0.086900386822
  | 4 => 0.087830218348
  | 5 => 0.088759615949
  | 6 => 0.089690271908
  | 7 => 0.090624208640
  | 8 => 0.091563824509
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12861 12861 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12861 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12861

/-! Actual upper energy certificates on all 43 source endpoints at 12861. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12861)
open BstLean.Part268 (cell12861)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12861 (gMinus 12861) (1 - (cell12861 i).lower) ≤ 1 ∧
    energyUpper 12861 (gMinus 12861) (BstLean.Part211.gPlus 12861)
      (finiteEnergy 12861 12861 0.011) (1 - (cell12861 i).lower) ≤
      (cell12861 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨10,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨11,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨12,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨13,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨14,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨15,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨16,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨17,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨18,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨19,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨20,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨21,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨22,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨23,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨24,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨25,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨26,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨27,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨28,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨29,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨30,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨31,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨32,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨33,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨34,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨35,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨36,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨37,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨38,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨39,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨40,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨41,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨42,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨43,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨44,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨45,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨46,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨47,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨48,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨49,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨50,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨51,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12861) (by norm_num)
        (q := 1 - (cell12861 ⟨52,by decide⟩).lower)
        (by norm_num [cell12861]) (by norm_num [cell12861])
      exact ⟨E.1,E.2.trans (by norm_num [cell12861])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12861

/-! Source-cell containment and simple scalar guards at 12861. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12861)
open BstLean.Part268 (cell12861)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12861 ⟨10,by decide⟩).lower ∧ (cell12861 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12861 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12861 ⟨11,by decide⟩).lower ∧ (cell12861 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12861 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12861 ⟨12,by decide⟩).lower ∧ (cell12861 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12861 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12861 ⟨13,by decide⟩).lower ∧ (cell12861 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12861 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12861 ⟨14,by decide⟩).lower ∧ (cell12861 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12861 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12861 ⟨15,by decide⟩).lower ∧ (cell12861 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12861 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12861 ⟨16,by decide⟩).lower ∧ (cell12861 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12861 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12861 ⟨17,by decide⟩).lower ∧ (cell12861 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12861 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12861 ⟨18,by decide⟩).lower ∧ (cell12861 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12861 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12861 ⟨19,by decide⟩).lower ∧ (cell12861 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12861 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12861 ⟨20,by decide⟩).lower ∧ (cell12861 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12861 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12861 ⟨21,by decide⟩).lower ∧ (cell12861 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12861 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12861 ⟨22,by decide⟩).lower ∧ (cell12861 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12861 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12861 ⟨23,by decide⟩).lower ∧ (cell12861 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12861 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12861 ⟨24,by decide⟩).lower ∧ (cell12861 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12861 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12861 ⟨25,by decide⟩).lower ∧ (cell12861 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12861 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12861 ⟨26,by decide⟩).lower ∧ (cell12861 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12861 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12861 ⟨27,by decide⟩).lower ∧ (cell12861 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12861 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12861 ⟨28,by decide⟩).lower ∧ (cell12861 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12861 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12861 ⟨29,by decide⟩).lower ∧ (cell12861 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12861 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12861 ⟨30,by decide⟩).lower ∧ (cell12861 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12861 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12861 ⟨31,by decide⟩).lower ∧ (cell12861 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12861 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12861 ⟨32,by decide⟩).lower ∧ (cell12861 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12861 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12861 ⟨33,by decide⟩).lower ∧ (cell12861 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12861 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12861 ⟨34,by decide⟩).lower ∧ (cell12861 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12861 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12861 ⟨35,by decide⟩).lower ∧ (cell12861 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12861 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12861 ⟨36,by decide⟩).lower ∧ (cell12861 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12861 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12861 ⟨37,by decide⟩).lower ∧ (cell12861 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12861 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12861 ⟨38,by decide⟩).lower ∧ (cell12861 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12861 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12861 ⟨39,by decide⟩).lower ∧ (cell12861 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12861 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12861 ⟨40,by decide⟩).lower ∧ (cell12861 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12861 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12861 ⟨41,by decide⟩).lower ∧ (cell12861 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12861 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12861 ⟨42,by decide⟩).lower ∧ (cell12861 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12861 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12861 ⟨43,by decide⟩).lower ∧ (cell12861 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12861 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12861 ⟨44,by decide⟩).lower ∧ (cell12861 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12861 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12861 ⟨45,by decide⟩).lower ∧ (cell12861 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12861 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12861 ⟨46,by decide⟩).lower ∧ (cell12861 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12861 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12861 ⟨47,by decide⟩).lower ∧ (cell12861 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12861 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12861 ⟨48,by decide⟩).lower ∧ (cell12861 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12861 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12861 ⟨49,by decide⟩).lower ∧ (cell12861 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12861 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12861 ⟨50,by decide⟩).lower ∧ (cell12861 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12861 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12861 ⟨51,by decide⟩).lower ∧ (cell12861 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12861 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12861 ⟨52,by decide⟩).lower ∧ (cell12861 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12861 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12861 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12861 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12861,cell12861,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12861 i).lower ∧
    (cell12861 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12861 i).upper ≤ (0.532 : ℝ) ∧
    (cell12861 i).centre ≤ (0.1 : ℝ) ∧ (cell12861 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12861 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12861 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12861

/-! The local source numeric instances at 12861 have no network premises. -/
namespace BstLean.Part269.N12861
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12861)
open BstLean.Part268 (cell12861)

noncomputable def sourceNumerics12861 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12861 (cell12861 i)
      scalarRow12861.M scalarRow12861.H scalarRow12861.xi := by
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
    energy_allowance := scalarRow12861.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12861]
    centre_nonneg := (scalarRow12861.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12861])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12861
/-! Actual 12862 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12862 ≤ (1.035581016286 : ℝ) := by
  have hr : (113.410757867144 : ℝ) ≤ √(12862 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.410757867144 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12862 12862 (11 / 1000) ≤
    (0.008428538887 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12862) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.410757867144 : ℝ) ≤ √(12862 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12862)
  have hdiv : K / √(12862 : ℝ) ≤ K / 113.410757867144 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.410757867144 ≤ (0.008428538887 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12862.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12862 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12862 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12862 := gPlus_lower 12862
end BstLean.Part269.N12862

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12862
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035581016285 : ℝ) ≤ wn 12862 := by
  have hn : √(12862 : ℝ) ≤ 113.410757867145 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12862 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.410757867145 ≤ 2 / √(12862 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248653574 : ℝ) ≤ rhoBar 12862 BstLean.Part154.csC ∧
    rhoBar 12862 BstLean.Part154.csC ≤ 0.000248653959 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035581016285 : ℝ) / (1.295212 * 12862) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035581016286 : ℝ) / (1.29521 * 12862) := by gcongr
      _ ≤ (0.000248653959 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12862 BstLean.Part154.csC) ≤ 0.000994677665 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12862 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) ≤ 0.000189923458 ∧
    cc1 (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) ≤ 0.000120849581 ∧
    cc2 (rhoBar 12862 BstLean.Part154.csC) ≤ 0.000070154136 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12862 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12862 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12862 BstLean.Part154.csC * nuR (rhoBar 12862 BstLean.Part154.csC)) ≤ 0.000497323376 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248653959 : ℝ) * 0.000994677665 := by gcongr
      _ ≤ (0.000497323376 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12862 BstLean.Part154.csC) * nuR (rhoBar 12862 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994677665 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12862 BstLean.Part154.csC) * rhoBar 12862 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248653959 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248653959 / 2 + 0.399 * 0.000994677665 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189923458 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497323376 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120849581 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248653959 / 1.414213562 := by gcongr
      _ ≤ (0.000070154136 : ℝ) := by norm_num

end BstLean.Part269.N12862

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12862
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) ≤ 1.55773E-7 := by
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12862 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12862 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12862 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189923458 : ℝ) ^ 2 + 0.000120849581 ^ 2 + 3 * 0.000070154136 ^ 2 +
        2 * 0.797885 * 0.000189923458 * 0.000120849581 + 2 * 0.000189923458 * 0.000070154136 +
        4 * 0.797885 * 0.000120849581 * 0.000070154136 := by gcongr
    _ ≤ (1.55773E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12862 BstLean.Part154.csC Θ ≤ 0.002595025024 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12862 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12862 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12862 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035581016286 * 1.55773E-7 / (0.000248653574 : ℝ) := by gcongr
    _ ≤ 0.002595025024 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12862 BstLean.Part154.csC Θ ≤ 0.002878687608 + 0.000655721863 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12862 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12862 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035581016286 : ℝ) * ((2 * Θ * 0.000248653959 +
        (6863 / 10000) * 0.000248653959 * 12862 * 0.000994677665) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002878687608 + 0.000655721863 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12862 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12862 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12862 0.011 Θ ∧ gammaRatio 12862 0.011 Θ ≤ 0.000085480801 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12862 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035581016286 : ℝ) * 0.525 / ((1 - 0.011) * 12862) := by gcongr
      _ ≤ (0.000085480801 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12862 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12862 0.011 Θ) :=
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
    badAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12862 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12862 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12862 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12862 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12862 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12862 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12862 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12862 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12862 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12862 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035581016286 : ℝ) * 12862 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003361430770 + 0.003250746887 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12862

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12862
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12862 BstLean.Part154.csC) (piBar (rhoBar 12862 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12862 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12862 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12862 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12862 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12862 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12862 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12862 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12862 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12862 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12862 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052149166427 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12862) ≤ 0.010530196637 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12862 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035581016286)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010530196637 + 2 * 0.737676 / 12862) := by gcongr
    _ ≤ (0.052149166427 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12862 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12862

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12862
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510802138 : ℝ) ≤ plow 12862 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12862) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574672886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362388138) : eMP 12862 0.011 xi bn ≤ 0.001173104585 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12862 : ℝ) * (1 - 0.011))) ≤ 0.000580060095 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362388138 / (12862 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580060095 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580060095 : ℝ) + 3.141593 * 0.052574672886 / (12862 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173104585 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574672886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362388138) : PiBarMP 12862 12 0.011 xi bn ≤ 0.160222013369 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12862 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036910542370 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.785273861439 : ℝ) ≤ √((12862 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.410757867144 : ℝ) ≤ √(12862 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12862) ≤ 0.122849088789 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036910542370 + 0.052574672886 * 1.772454 / (2 * (112.785273861439 : ℝ))) * (1 + 0.001173104585) +
        8 / (12862 * 113.410757867144) + 0.122849088789 := by gcongr
    _ ≤ (0.160222013369 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574672886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362388138) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281440842870) :
    parallelOracle 12862 0.011 xi bn cd ≤ 0.161199722711 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12862 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12862 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510802138 : ℝ) ≤ plow 12862 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.410757867144 : ℝ) ≤ √(12862 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281440842870 : ℝ) / (2 * 0.560510802138 * 113.410757867144)) * 0.160222013369 +
        0.281440842870 ^ 2 / (2 * 0.560510802138 * 113.410757867144) := by gcongr
    _ ≤ (0.161199722711 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574672886) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362388138)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281440842870) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12862 12862 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510802138 : ℝ) ≤ plow 12862 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.410757867144 : ℝ) ≤ √(12862 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12862 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12862 Θ 1.22 ≤ 0.011692898672 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.410757867144 := by gcongr <;> linarith
      _ ≤ (0.011692898672 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12862 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12862 12862 0.011 ≤ 0.008428538887 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12862 12862 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12862 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12862 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12862 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12862 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161199722711 + 0.011692898672 + (0.008428538887 : ℝ) *
        (1 + 2 * (0.281440842870 + 0.011692898672) / (0.560510802138 * 113.410757867144))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12862]

end BstLean.Part269.N12862

/-! The original eight local profiles supply actual 12862 moment certificates. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12862 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052574672886 ∧
    0 ≤ bN 12862 BstLean.Part154.csC (groupTheta g) ∧ bN 12862 BstLean.Part154.csC (groupTheta g) ≤ 0.001362388138 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12862 12862 0.011
      (momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12862 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12862 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12862 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229291676443 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12862 0.011
      (momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12862 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12862
/-! The actual computed-centre upper energy formula at 12862. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12862

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12862)
open BstLean.Part268 (cell12862)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085031300971
  | 2 => 0.085965915559
  | 3 => 0.086897531730
  | 4 => 0.087827302092
  | 5 => 0.088756628996
  | 6 => 0.089687202663
  | 7 => 0.090621043108
  | 8 => 0.091560545913
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12862 12862 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12862 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12862

/-! Actual upper energy certificates on all 43 source endpoints at 12862. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12862)
open BstLean.Part268 (cell12862)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12862 (gMinus 12862) (1 - (cell12862 i).lower) ≤ 1 ∧
    energyUpper 12862 (gMinus 12862) (BstLean.Part211.gPlus 12862)
      (finiteEnergy 12862 12862 0.011) (1 - (cell12862 i).lower) ≤
      (cell12862 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨10,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨11,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨12,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨13,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨14,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨15,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨16,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨17,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨18,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨19,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨20,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨21,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨22,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨23,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨24,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨25,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨26,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨27,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨28,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨29,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨30,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨31,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨32,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨33,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨34,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨35,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨36,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨37,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨38,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨39,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨40,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨41,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨42,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨43,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨44,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨45,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨46,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨47,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨48,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨49,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨50,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨51,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12862) (by norm_num)
        (q := 1 - (cell12862 ⟨52,by decide⟩).lower)
        (by norm_num [cell12862]) (by norm_num [cell12862])
      exact ⟨E.1,E.2.trans (by norm_num [cell12862])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12862

/-! Source-cell containment and simple scalar guards at 12862. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12862)
open BstLean.Part268 (cell12862)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12862 ⟨10,by decide⟩).lower ∧ (cell12862 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12862 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12862 ⟨11,by decide⟩).lower ∧ (cell12862 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12862 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12862 ⟨12,by decide⟩).lower ∧ (cell12862 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12862 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12862 ⟨13,by decide⟩).lower ∧ (cell12862 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12862 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12862 ⟨14,by decide⟩).lower ∧ (cell12862 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12862 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12862 ⟨15,by decide⟩).lower ∧ (cell12862 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12862 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12862 ⟨16,by decide⟩).lower ∧ (cell12862 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12862 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12862 ⟨17,by decide⟩).lower ∧ (cell12862 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12862 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12862 ⟨18,by decide⟩).lower ∧ (cell12862 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12862 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12862 ⟨19,by decide⟩).lower ∧ (cell12862 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12862 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12862 ⟨20,by decide⟩).lower ∧ (cell12862 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12862 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12862 ⟨21,by decide⟩).lower ∧ (cell12862 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12862 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12862 ⟨22,by decide⟩).lower ∧ (cell12862 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12862 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12862 ⟨23,by decide⟩).lower ∧ (cell12862 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12862 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12862 ⟨24,by decide⟩).lower ∧ (cell12862 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12862 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12862 ⟨25,by decide⟩).lower ∧ (cell12862 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12862 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12862 ⟨26,by decide⟩).lower ∧ (cell12862 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12862 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12862 ⟨27,by decide⟩).lower ∧ (cell12862 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12862 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12862 ⟨28,by decide⟩).lower ∧ (cell12862 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12862 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12862 ⟨29,by decide⟩).lower ∧ (cell12862 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12862 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12862 ⟨30,by decide⟩).lower ∧ (cell12862 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12862 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12862 ⟨31,by decide⟩).lower ∧ (cell12862 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12862 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12862 ⟨32,by decide⟩).lower ∧ (cell12862 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12862 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12862 ⟨33,by decide⟩).lower ∧ (cell12862 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12862 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12862 ⟨34,by decide⟩).lower ∧ (cell12862 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12862 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12862 ⟨35,by decide⟩).lower ∧ (cell12862 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12862 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12862 ⟨36,by decide⟩).lower ∧ (cell12862 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12862 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12862 ⟨37,by decide⟩).lower ∧ (cell12862 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12862 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12862 ⟨38,by decide⟩).lower ∧ (cell12862 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12862 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12862 ⟨39,by decide⟩).lower ∧ (cell12862 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12862 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12862 ⟨40,by decide⟩).lower ∧ (cell12862 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12862 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12862 ⟨41,by decide⟩).lower ∧ (cell12862 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12862 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12862 ⟨42,by decide⟩).lower ∧ (cell12862 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12862 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12862 ⟨43,by decide⟩).lower ∧ (cell12862 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12862 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12862 ⟨44,by decide⟩).lower ∧ (cell12862 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12862 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12862 ⟨45,by decide⟩).lower ∧ (cell12862 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12862 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12862 ⟨46,by decide⟩).lower ∧ (cell12862 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12862 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12862 ⟨47,by decide⟩).lower ∧ (cell12862 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12862 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12862 ⟨48,by decide⟩).lower ∧ (cell12862 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12862 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12862 ⟨49,by decide⟩).lower ∧ (cell12862 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12862 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12862 ⟨50,by decide⟩).lower ∧ (cell12862 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12862 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12862 ⟨51,by decide⟩).lower ∧ (cell12862 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12862 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12862 ⟨52,by decide⟩).lower ∧ (cell12862 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12862 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12862 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12862 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12862,cell12862,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12862 i).lower ∧
    (cell12862 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12862 i).upper ≤ (0.532 : ℝ) ∧
    (cell12862 i).centre ≤ (0.1 : ℝ) ∧ (cell12862 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12862 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12862 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12862

/-! The local source numeric instances at 12862 have no network premises. -/
namespace BstLean.Part269.N12862
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12862)
open BstLean.Part268 (cell12862)

noncomputable def sourceNumerics12862 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12862 (cell12862 i)
      scalarRow12862.M scalarRow12862.H scalarRow12862.xi := by
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
    energy_allowance := scalarRow12862.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12862]
    centre_nonneg := (scalarRow12862.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12862])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12862