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
import BstLean.Part269Direction13
import BstLean.Part269Shared13
import BstLean.Part269Finite
import BstLean.Part269Rows13
import BstLean.Part269Source
/-! Actual 12675 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12675 ≤ (1.035844829189 : ℝ) := by
  have hr : (112.583302491977 : ℝ) ≤ √(12675 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.583302491977 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12675 12675 (11 / 1000) ≤
    (0.008490486735 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12675) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.583302491977 : ℝ) ≤ √(12675 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12675)
  have hdiv : K / √(12675 : ℝ) ≤ K / 112.583302491977 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.583302491977 ≤ (0.008490486735 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12675.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12675 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12675 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12675 := gPlus_lower 12675
end BstLean.Part269.N12675

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12675
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035844829188 : ℝ) ≤ wn 12675 := by
  have hn : √(12675 : ℝ) ≤ 112.583302491978 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12675 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.583302491978 ≤ 2 / √(12675 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252386351 : ℝ) ≤ rhoBar 12675 BstLean.Part154.csC ∧
    rhoBar 12675 BstLean.Part154.csC ≤ 0.000252386742 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035844829188 : ℝ) / (1.295212 * 12675) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035844829189 : ℝ) / (1.29521 * 12675) := by gcongr
      _ ≤ (0.000252386742 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12675 BstLean.Part154.csC) ≤ 0.001009610668 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12675 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) ≤ 0.000192774714 ∧
    cc1 (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) ≤ 0.000122663827 ∧
    cc2 (rhoBar 12675 BstLean.Part154.csC) ≤ 0.000071207287 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12675 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12675 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12675 BstLean.Part154.csC * nuR (rhoBar 12675 BstLean.Part154.csC)) ≤ 0.000504789409 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252386742 : ℝ) * 0.001009610668 := by gcongr
      _ ≤ (0.000504789409 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12675 BstLean.Part154.csC) * nuR (rhoBar 12675 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009610668 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12675 BstLean.Part154.csC) * rhoBar 12675 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252386742 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252386742 / 2 + 0.399 * 0.001009610668 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192774714 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504789409 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122663827 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252386742 / 1.414213562 := by gcongr
      _ ≤ (0.000071207287 : ℝ) := by norm_num

end BstLean.Part269.N12675

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12675
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) ≤ 1.60485E-7 := by
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12675 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12675 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12675 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192774714 : ℝ) ^ 2 + 0.000122663827 ^ 2 + 3 * 0.000071207287 ^ 2 +
        2 * 0.797885 * 0.000192774714 * 0.000122663827 + 2 * 0.000192774714 * 0.000071207287 +
        4 * 0.797885 * 0.000122663827 * 0.000071207287 := by gcongr
    _ ≤ (1.60485E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12675 BstLean.Part154.csC Θ ≤ 0.002634652100 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12675 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12675 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12675 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035844829189 * 1.60485E-7 / (0.000252386351 : ℝ) := by gcongr
    _ ≤ 0.002634652100 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12675 BstLean.Part154.csC Θ ≤ 0.002923393969 + 0.000665735084 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12675 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12675 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035844829189 : ℝ) * ((2 * Θ * 0.000252386742 +
        (6863 / 10000) * 0.000252386742 * 12675 * 0.001009610668) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002923393969 + 0.000665735084 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12675 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12675 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12675 0.011 Θ ∧ gammaRatio 12675 0.011 Θ ≤ 0.000086764036 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12675 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035844829189 : ℝ) * 0.525 / ((1 - 0.011) * 12675) := by gcongr
      _ ≤ (0.000086764036 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12675 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12675 0.011 Θ) :=
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
    badAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12675 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12675 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12675 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12675 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12675 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12675 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12675 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12675 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12675 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12675 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035844829189 : ℝ) * 12675 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538895953 + 0.003300387184 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12675

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12675
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12675 BstLean.Part154.csC) (piBar (rhoBar 12675 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12675 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12675 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12675 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12675 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12675 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12675 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12675 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12675 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12675 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12675 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052536608508 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12675) ≤ 0.010607590599 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12675 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035844829189)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010607590599 + 2 * 0.737676 / 12675) := by gcongr
    _ ≤ (0.052536608508 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12675 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12675

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12675
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502435487 : ℝ) ≤ plow 12675 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12675) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778199225)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383192353) : eMP 12675 0.011 xi bn ≤ 0.001190762756 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12675 : ℝ) * (1 - 0.011))) ≤ 0.000588767895 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383192353 / (12675 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588767895 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588767895 : ℝ) + 3.141593 * 0.052778199225 / (12675 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190762756 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778199225)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383192353) : PiBarMP 12675 12 0.011 xi bn ≤ 0.161411439028 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12675 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037191294049 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.962382075409 : ℝ) ≤ √((12675 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.583302491977 : ℝ) ≤ √(12675 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12675) ≤ 0.123751994784 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037191294049 + 0.052778199225 * 1.772454 / (2 * (111.962382075409 : ℝ))) * (1 + 0.001190762756) +
        8 / (12675 * 112.583302491977) + 0.123751994784 := by gcongr
    _ ≤ (0.161411439028 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778199225)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383192353) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282271671625) :
    parallelOracle 12675 0.011 xi bn cd ≤ 0.162403774941 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12675 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12675 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502435487 : ℝ) ≤ plow 12675 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.583302491977 : ℝ) ≤ √(12675 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282271671625 : ℝ) / (2 * 0.560502435487 * 112.583302491977)) * 0.161411439028 +
        0.282271671625 ^ 2 / (2 * 0.560502435487 * 112.583302491977) := by gcongr
    _ ≤ (0.162403774941 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778199225) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383192353)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282271671625) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12675 12675 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502435487 : ℝ) ≤ plow 12675 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.583302491977 : ℝ) ≤ √(12675 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12675 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12675 Θ 1.22 ≤ 0.011778838164 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.583302491977 := by gcongr <;> linarith
      _ ≤ (0.011778838164 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12675 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12675 12675 0.011 ≤ 0.008490486735 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12675 12675 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12675 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12675 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12675 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12675 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162403774941 + 0.011778838164 + (0.008490486735 : ℝ) *
        (1 + 2 * (0.282271671625 + 0.011778838164) / (0.560502435487 * 112.583302491977))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12675]

end BstLean.Part269.N12675

/-! The original eight local profiles supply actual 12675 moment certificates. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12675 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052778199225 ∧
    0 ≤ bN 12675 BstLean.Part154.csC (groupTheta g) ∧ bN 12675 BstLean.Part154.csC (groupTheta g) ≤ 0.001383192353 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12675 12675 0.011
      (momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12675 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12675 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12675 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229735063117 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12675 0.011
      (momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12675 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12675
/-! The actual computed-centre upper energy formula at 12675. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12675

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12675)
open BstLean.Part268 (cell12675)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085563505190
  | 2 => 0.086507607974
  | 3 => 0.087450049093
  | 4 => 0.088392292296
  | 5 => 0.089336106539
  | 6 => 0.090283611128
  | 7 => 0.091237325059
  | 8 => 0.092200220611
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12675 12675 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12675 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12675

/-! Actual upper energy certificates on all 43 source endpoints at 12675. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12675)
open BstLean.Part268 (cell12675)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12675 (gMinus 12675) (1 - (cell12675 i).lower) ≤ 1 ∧
    energyUpper 12675 (gMinus 12675) (BstLean.Part211.gPlus 12675)
      (finiteEnergy 12675 12675 0.011) (1 - (cell12675 i).lower) ≤
      (cell12675 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨10,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨11,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨12,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨13,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨14,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨15,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨16,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨17,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨18,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨19,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨20,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨21,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨22,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨23,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨24,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨25,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨26,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨27,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨28,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨29,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨30,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨31,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨32,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨33,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨34,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨35,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨36,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨37,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨38,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨39,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨40,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨41,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨42,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨43,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨44,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨45,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨46,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨47,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨48,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨49,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨50,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨51,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12675) (by norm_num)
        (q := 1 - (cell12675 ⟨52,by decide⟩).lower)
        (by norm_num [cell12675]) (by norm_num [cell12675])
      exact ⟨E.1,E.2.trans (by norm_num [cell12675])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12675

/-! Source-cell containment and simple scalar guards at 12675. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12675)
open BstLean.Part268 (cell12675)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12675 ⟨10,by decide⟩).lower ∧ (cell12675 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12675 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12675 ⟨11,by decide⟩).lower ∧ (cell12675 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12675 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12675 ⟨12,by decide⟩).lower ∧ (cell12675 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12675 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12675 ⟨13,by decide⟩).lower ∧ (cell12675 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12675 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12675 ⟨14,by decide⟩).lower ∧ (cell12675 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12675 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12675 ⟨15,by decide⟩).lower ∧ (cell12675 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12675 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12675 ⟨16,by decide⟩).lower ∧ (cell12675 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12675 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12675 ⟨17,by decide⟩).lower ∧ (cell12675 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12675 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12675 ⟨18,by decide⟩).lower ∧ (cell12675 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12675 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12675 ⟨19,by decide⟩).lower ∧ (cell12675 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12675 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12675 ⟨20,by decide⟩).lower ∧ (cell12675 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12675 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12675 ⟨21,by decide⟩).lower ∧ (cell12675 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12675 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12675 ⟨22,by decide⟩).lower ∧ (cell12675 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12675 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12675 ⟨23,by decide⟩).lower ∧ (cell12675 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12675 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12675 ⟨24,by decide⟩).lower ∧ (cell12675 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12675 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12675 ⟨25,by decide⟩).lower ∧ (cell12675 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12675 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12675 ⟨26,by decide⟩).lower ∧ (cell12675 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12675 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12675 ⟨27,by decide⟩).lower ∧ (cell12675 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12675 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12675 ⟨28,by decide⟩).lower ∧ (cell12675 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12675 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12675 ⟨29,by decide⟩).lower ∧ (cell12675 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12675 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12675 ⟨30,by decide⟩).lower ∧ (cell12675 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12675 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12675 ⟨31,by decide⟩).lower ∧ (cell12675 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12675 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12675 ⟨32,by decide⟩).lower ∧ (cell12675 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12675 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12675 ⟨33,by decide⟩).lower ∧ (cell12675 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12675 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12675 ⟨34,by decide⟩).lower ∧ (cell12675 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12675 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12675 ⟨35,by decide⟩).lower ∧ (cell12675 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12675 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12675 ⟨36,by decide⟩).lower ∧ (cell12675 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12675 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12675 ⟨37,by decide⟩).lower ∧ (cell12675 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12675 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12675 ⟨38,by decide⟩).lower ∧ (cell12675 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12675 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12675 ⟨39,by decide⟩).lower ∧ (cell12675 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12675 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12675 ⟨40,by decide⟩).lower ∧ (cell12675 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12675 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12675 ⟨41,by decide⟩).lower ∧ (cell12675 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12675 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12675 ⟨42,by decide⟩).lower ∧ (cell12675 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12675 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12675 ⟨43,by decide⟩).lower ∧ (cell12675 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12675 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12675 ⟨44,by decide⟩).lower ∧ (cell12675 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12675 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12675 ⟨45,by decide⟩).lower ∧ (cell12675 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12675 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12675 ⟨46,by decide⟩).lower ∧ (cell12675 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12675 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12675 ⟨47,by decide⟩).lower ∧ (cell12675 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12675 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12675 ⟨48,by decide⟩).lower ∧ (cell12675 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12675 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12675 ⟨49,by decide⟩).lower ∧ (cell12675 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12675 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12675 ⟨50,by decide⟩).lower ∧ (cell12675 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12675 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12675 ⟨51,by decide⟩).lower ∧ (cell12675 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12675 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12675 ⟨52,by decide⟩).lower ∧ (cell12675 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12675 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12675 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12675 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12675,cell12675,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12675 i).lower ∧
    (cell12675 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12675 i).upper ≤ (0.532 : ℝ) ∧
    (cell12675 i).centre ≤ (0.1 : ℝ) ∧ (cell12675 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12675 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12675 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12675

/-! The local source numeric instances at 12675 have no network premises. -/
namespace BstLean.Part269.N12675
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12675)
open BstLean.Part268 (cell12675)

noncomputable def sourceNumerics12675 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12675 (cell12675 i)
      scalarRow12675.M scalarRow12675.H scalarRow12675.xi := by
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
    energy_allowance := scalarRow12675.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12675]
    centre_nonneg := (scalarRow12675.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12675])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12675
/-! Actual 12676 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12676 ≤ (1.035843402828 : ℝ) := by
  have hr : (112.587743560300 : ℝ) ≤ √(12676 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.587743560300 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12676 12676 (11 / 1000) ≤
    (0.008490151822 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12676) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.587743560300 : ℝ) ≤ √(12676 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12676)
  have hdiv : K / √(12676 : ℝ) ≤ K / 112.587743560300 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.587743560300 ≤ (0.008490151822 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12676.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12676 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12676 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12676 := gPlus_lower 12676
end BstLean.Part269.N12676

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12676
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035843402827 : ℝ) ≤ wn 12676 := by
  have hn : √(12676 : ℝ) ≤ 112.587743560301 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12676 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.587743560301 ≤ 2 / √(12676 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252366093 : ℝ) ≤ rhoBar 12676 BstLean.Part154.csC ∧
    rhoBar 12676 BstLean.Part154.csC ≤ 0.000252366484 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035843402827 : ℝ) / (1.295212 * 12676) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035843402828 : ℝ) / (1.29521 * 12676) := by gcongr
      _ ≤ (0.000252366484 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12676 BstLean.Part154.csC) ≤ 0.001009529625 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12676 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) ≤ 0.000192759240 ∧
    cc1 (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) ≤ 0.000122653981 ∧
    cc2 (rhoBar 12676 BstLean.Part154.csC) ≤ 0.000071201571 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12676 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12676 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12676 BstLean.Part154.csC * nuR (rhoBar 12676 BstLean.Part154.csC)) ≤ 0.000504748890 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252366484 : ℝ) * 0.001009529625 := by gcongr
      _ ≤ (0.000504748890 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12676 BstLean.Part154.csC) * nuR (rhoBar 12676 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009529625 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12676 BstLean.Part154.csC) * rhoBar 12676 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252366484 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252366484 / 2 + 0.399 * 0.001009529625 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192759240 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504748890 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122653981 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252366484 / 1.414213562 := by gcongr
      _ ≤ (0.000071201571 : ℝ) := by norm_num

end BstLean.Part269.N12676

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12676
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) ≤ 1.60460E-7 := by
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12676 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12676 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12676 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192759240 : ℝ) ^ 2 + 0.000122653981 ^ 2 + 3 * 0.000071201571 ^ 2 +
        2 * 0.797885 * 0.000192759240 * 0.000122653981 + 2 * 0.000192759240 * 0.000071201571 +
        4 * 0.797885 * 0.000122653981 * 0.000071201571 := by gcongr
    _ ≤ (1.60460E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12676 BstLean.Part154.csC Θ ≤ 0.002634449509 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12676 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12676 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12676 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035843402828 * 1.60460E-7 / (0.000252366093 : ℝ) := by gcongr
    _ ≤ 0.002634449509 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12676 BstLean.Part154.csC Θ ≤ 0.002923151255 + 0.000665680732 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12676 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12676 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035843402828 : ℝ) * ((2 * Θ * 0.000252366484 +
        (6863 / 10000) * 0.000252366484 * 12676 * 0.001009529625) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002923151255 + 0.000665680732 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12676 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12676 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12676 0.011 Θ ∧ gammaRatio 12676 0.011 Θ ≤ 0.000086757071 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12676 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035843402828 : ℝ) * 0.525 / ((1 - 0.011) * 12676) := by gcongr
      _ ≤ (0.000086757071 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12676 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12676 0.011 Θ) :=
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
    badAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12676 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12676 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12676 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12676 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12676 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12676 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12676 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12676 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12676 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12676 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035843402828 : ℝ) * 12676 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538653239 + 0.003300130241 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12676

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12676
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12676 BstLean.Part154.csC) (piBar (rhoBar 12676 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12676 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12676 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12676 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12676 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12676 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12676 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12676 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12676 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12676 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12676 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052534513687 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12676) ≤ 0.010607172178 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12676 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035843402828)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010607172178 + 2 * 0.737676 / 12676) := by gcongr
    _ ≤ (0.052534513687 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12676 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12676

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12676
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502480885 : ℝ) ≤ plow 12676 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12676) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777821616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383085993) : eMP 12676 0.011 xi bn ≤ 0.001190669898 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12676 : ℝ) * (1 - 0.011))) ≤ 0.000588722035 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383085993 / (12676 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588722035 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588722035 : ℝ) + 3.141593 * 0.052777821616 / (12676 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190669898 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777821616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383085993) : PiBarMP 12676 12 0.011 xi bn ≤ 0.161405102301 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12676 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037189864117 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.966798650314 : ℝ) ≤ √((12676 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.587743560300 : ℝ) ≤ √(12676 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12676) ≤ 0.123747113338 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037189864117 + 0.052777821616 * 1.772454 / (2 * (111.966798650314 : ℝ))) * (1 + 0.001190669898) +
        8 / (12676 * 112.587743560300) + 0.123747113338 := by gcongr
    _ ≤ (0.161405102301 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777821616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383085993) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282268754966) :
    parallelOracle 12676 0.011 xi bn cd ≤ 0.162397368042 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12676 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12676 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502480885 : ℝ) ≤ plow 12676 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.587743560300 : ℝ) ≤ √(12676 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282268754966 : ℝ) / (2 * 0.560502480885 * 112.587743560300)) * 0.161405102301 +
        0.282268754966 ^ 2 / (2 * 0.560502480885 * 112.587743560300) := by gcongr
    _ ≤ (0.162397368042 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777821616) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383085993)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282268754966) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12676 12676 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502480885 : ℝ) ≤ plow 12676 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.587743560300 : ℝ) ≤ √(12676 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12676 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12676 Θ 1.22 ≤ 0.011778373543 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.587743560300 := by gcongr <;> linarith
      _ ≤ (0.011778373543 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12676 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12676 12676 0.011 ≤ 0.008490151822 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12676 12676 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12676 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12676 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12676 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12676 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162397368042 + 0.011778373543 + (0.008490151822 : ℝ) *
        (1 + 2 * (0.282268754966 + 0.011778373543) / (0.560502480885 * 112.587743560300))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12676]

end BstLean.Part269.N12676

/-! The original eight local profiles supply actual 12676 moment certificates. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12676 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052777821616 ∧
    0 ≤ bN 12676 BstLean.Part154.csC (groupTheta g) ∧ bN 12676 BstLean.Part154.csC (groupTheta g) ≤ 0.001383085993 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12676 12676 0.011
      (momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12676 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12676 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12676 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229734241279 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12676 0.011
      (momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12676 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12676
/-! The actual computed-centre upper energy formula at 12676. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12676

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12676)
open BstLean.Part268 (cell12676)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085560562006
  | 2 => 0.086504610103
  | 3 => 0.087446988460
  | 4 => 0.088389158970
  | 5 => 0.089332888412
  | 6 => 0.090280293545
  | 7 => 0.091233890410
  | 8 => 0.092196647879
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12676 12676 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12676 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12676

/-! Actual upper energy certificates on all 43 source endpoints at 12676. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12676)
open BstLean.Part268 (cell12676)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12676 (gMinus 12676) (1 - (cell12676 i).lower) ≤ 1 ∧
    energyUpper 12676 (gMinus 12676) (BstLean.Part211.gPlus 12676)
      (finiteEnergy 12676 12676 0.011) (1 - (cell12676 i).lower) ≤
      (cell12676 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨10,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨11,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨12,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨13,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨14,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨15,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨16,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨17,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨18,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨19,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨20,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨21,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨22,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨23,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨24,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨25,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨26,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨27,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨28,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨29,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨30,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨31,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨32,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨33,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨34,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨35,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨36,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨37,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨38,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨39,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨40,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨41,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨42,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨43,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨44,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨45,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨46,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨47,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨48,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨49,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨50,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨51,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12676) (by norm_num)
        (q := 1 - (cell12676 ⟨52,by decide⟩).lower)
        (by norm_num [cell12676]) (by norm_num [cell12676])
      exact ⟨E.1,E.2.trans (by norm_num [cell12676])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12676

/-! Source-cell containment and simple scalar guards at 12676. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12676)
open BstLean.Part268 (cell12676)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12676 ⟨10,by decide⟩).lower ∧ (cell12676 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12676 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12676 ⟨11,by decide⟩).lower ∧ (cell12676 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12676 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12676 ⟨12,by decide⟩).lower ∧ (cell12676 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12676 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12676 ⟨13,by decide⟩).lower ∧ (cell12676 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12676 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12676 ⟨14,by decide⟩).lower ∧ (cell12676 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12676 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12676 ⟨15,by decide⟩).lower ∧ (cell12676 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12676 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12676 ⟨16,by decide⟩).lower ∧ (cell12676 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12676 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12676 ⟨17,by decide⟩).lower ∧ (cell12676 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12676 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12676 ⟨18,by decide⟩).lower ∧ (cell12676 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12676 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12676 ⟨19,by decide⟩).lower ∧ (cell12676 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12676 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12676 ⟨20,by decide⟩).lower ∧ (cell12676 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12676 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12676 ⟨21,by decide⟩).lower ∧ (cell12676 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12676 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12676 ⟨22,by decide⟩).lower ∧ (cell12676 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12676 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12676 ⟨23,by decide⟩).lower ∧ (cell12676 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12676 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12676 ⟨24,by decide⟩).lower ∧ (cell12676 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12676 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12676 ⟨25,by decide⟩).lower ∧ (cell12676 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12676 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12676 ⟨26,by decide⟩).lower ∧ (cell12676 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12676 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12676 ⟨27,by decide⟩).lower ∧ (cell12676 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12676 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12676 ⟨28,by decide⟩).lower ∧ (cell12676 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12676 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12676 ⟨29,by decide⟩).lower ∧ (cell12676 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12676 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12676 ⟨30,by decide⟩).lower ∧ (cell12676 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12676 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12676 ⟨31,by decide⟩).lower ∧ (cell12676 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12676 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12676 ⟨32,by decide⟩).lower ∧ (cell12676 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12676 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12676 ⟨33,by decide⟩).lower ∧ (cell12676 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12676 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12676 ⟨34,by decide⟩).lower ∧ (cell12676 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12676 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12676 ⟨35,by decide⟩).lower ∧ (cell12676 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12676 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12676 ⟨36,by decide⟩).lower ∧ (cell12676 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12676 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12676 ⟨37,by decide⟩).lower ∧ (cell12676 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12676 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12676 ⟨38,by decide⟩).lower ∧ (cell12676 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12676 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12676 ⟨39,by decide⟩).lower ∧ (cell12676 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12676 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12676 ⟨40,by decide⟩).lower ∧ (cell12676 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12676 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12676 ⟨41,by decide⟩).lower ∧ (cell12676 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12676 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12676 ⟨42,by decide⟩).lower ∧ (cell12676 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12676 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12676 ⟨43,by decide⟩).lower ∧ (cell12676 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12676 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12676 ⟨44,by decide⟩).lower ∧ (cell12676 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12676 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12676 ⟨45,by decide⟩).lower ∧ (cell12676 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12676 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12676 ⟨46,by decide⟩).lower ∧ (cell12676 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12676 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12676 ⟨47,by decide⟩).lower ∧ (cell12676 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12676 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12676 ⟨48,by decide⟩).lower ∧ (cell12676 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12676 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12676 ⟨49,by decide⟩).lower ∧ (cell12676 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12676 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12676 ⟨50,by decide⟩).lower ∧ (cell12676 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12676 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12676 ⟨51,by decide⟩).lower ∧ (cell12676 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12676 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12676 ⟨52,by decide⟩).lower ∧ (cell12676 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12676 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12676 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12676 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12676,cell12676,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12676 i).lower ∧
    (cell12676 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12676 i).upper ≤ (0.532 : ℝ) ∧
    (cell12676 i).centre ≤ (0.1 : ℝ) ∧ (cell12676 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12676 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12676 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12676

/-! The local source numeric instances at 12676 have no network premises. -/
namespace BstLean.Part269.N12676
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12676)
open BstLean.Part268 (cell12676)

noncomputable def sourceNumerics12676 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12676 (cell12676 i)
      scalarRow12676.M scalarRow12676.H scalarRow12676.xi := by
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
    energy_allowance := scalarRow12676.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12676]
    centre_nonneg := (scalarRow12676.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12676])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12676
/-! Actual 12677 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12677 ≤ (1.035841976636 : ℝ) := by
  have hr : (112.592184453451 : ℝ) ≤ √(12677 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.592184453451 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12677 12677 (11 / 1000) ≤
    (0.008489816948 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12677) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.592184453451 : ℝ) ≤ √(12677 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12677)
  have hdiv : K / √(12677 : ℝ) ≤ K / 112.592184453451 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.592184453451 ≤ (0.008489816948 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12677.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12677 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12677 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12677 := gPlus_lower 12677
end BstLean.Part269.N12677

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12677
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035841976635 : ℝ) ≤ wn 12677 := by
  have hn : √(12677 : ℝ) ≤ 112.592184453452 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12677 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.592184453452 ≤ 2 / √(12677 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252345839 : ℝ) ≤ rhoBar 12677 BstLean.Part154.csC ∧
    rhoBar 12677 BstLean.Part154.csC ≤ 0.000252346229 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035841976635 : ℝ) / (1.295212 * 12677) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035841976636 : ℝ) / (1.29521 * 12677) := by gcongr
      _ ≤ (0.000252346229 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12677 BstLean.Part154.csC) ≤ 0.001009448595 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12677 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) ≤ 0.000192743769 ∧
    cc1 (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) ≤ 0.000122644136 ∧
    cc2 (rhoBar 12677 BstLean.Part154.csC) ≤ 0.000071195857 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12677 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12677 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12677 BstLean.Part154.csC * nuR (rhoBar 12677 BstLean.Part154.csC)) ≤ 0.000504708378 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252346229 : ℝ) * 0.001009448595 := by gcongr
      _ ≤ (0.000504708378 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12677 BstLean.Part154.csC) * nuR (rhoBar 12677 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009448595 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12677 BstLean.Part154.csC) * rhoBar 12677 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252346229 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252346229 / 2 + 0.399 * 0.001009448595 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192743769 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504708378 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122644136 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252346229 / 1.414213562 := by gcongr
      _ ≤ (0.000071195857 : ℝ) := by norm_num

end BstLean.Part269.N12677

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12677
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) ≤ 1.60434E-7 := by
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12677 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12677 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12677 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192743769 : ℝ) ^ 2 + 0.000122644136 ^ 2 + 3 * 0.000071195857 ^ 2 +
        2 * 0.797885 * 0.000192743769 * 0.000122644136 + 2 * 0.000192743769 * 0.000071195857 +
        4 * 0.797885 * 0.000122644136 * 0.000071195857 := by gcongr
    _ ≤ (1.60434E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12677 BstLean.Part154.csC Θ ≤ 0.002634230426 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12677 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12677 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12677 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035841976636 * 1.60434E-7 / (0.000252345839 : ℝ) := by gcongr
    _ ≤ 0.002634230426 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12677 BstLean.Part154.csC Θ ≤ 0.002922908578 + 0.000665626388 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12677 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12677 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035841976636 : ℝ) * ((2 * Θ * 0.000252346229 +
        (6863 / 10000) * 0.000252346229 * 12677 * 0.001009448595) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002922908578 + 0.000665626388 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12677 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12677 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12677 0.011 Θ ∧ gammaRatio 12677 0.011 Θ ≤ 0.000086750108 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12677 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035841976636 : ℝ) * 0.525 / ((1 - 0.011) * 12677) := by gcongr
      _ ≤ (0.000086750108 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12677 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12677 0.011 Θ) :=
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
    badAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12677 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12677 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12677 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12677 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12677 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12677 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12677 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12677 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12677 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12677 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035841976636 : ℝ) * 12677 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538410562 + 0.003299856814 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12677

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12677
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12677 BstLean.Part154.csC) (piBar (rhoBar 12677 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12677 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12677 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12677 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12677 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12677 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12677 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12677 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12677 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12677 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12677 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052532419117 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12677) ≤ 0.010606753807 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12677 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035841976636)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010606753807 + 2 * 0.737676 / 12677) := by gcongr
    _ ≤ (0.052532419117 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12677 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12677

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12677
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502526275 : ℝ) ≤ plow 12677 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12677) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777435390)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382970974) : eMP 12677 0.011 xi bn ≤ 0.001190573360 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12677 : ℝ) * (1 - 0.011))) ≤ 0.000588674336 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382970974 / (12677 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588674336 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588674336 : ℝ) + 3.141593 * 0.052777435390 / (12677 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190573360 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777435390)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382970974) : PiBarMP 12677 12 0.011 xi bn ≤ 0.161398649332 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12677 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037188317709 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.971215051012 : ℝ) ≤ √((12677 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.592184453451 : ℝ) ≤ √(12677 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12677) ≤ 0.123742232469 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037188317709 + 0.052777435390 * 1.772454 / (2 * (111.971215051012 : ℝ))) * (1 + 0.001190573360) +
        8 / (12677 * 112.592184453451) + 0.123742232469 := by gcongr
    _ ≤ (0.161398649332 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777435390)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382970974) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282265819802) :
    parallelOracle 12677 0.011 xi bn cd ≤ 0.162390844543 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12677 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12677 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502526275 : ℝ) ≤ plow 12677 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.592184453451 : ℝ) ≤ √(12677 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282265819802 : ℝ) / (2 * 0.560502526275 * 112.592184453451)) * 0.161398649332 +
        0.282265819802 ^ 2 / (2 * 0.560502526275 * 112.592184453451) := by gcongr
    _ ≤ (0.162390844543 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777435390) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382970974)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282265819802) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12677 12677 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502526275 : ℝ) ≤ plow 12677 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.592184453451 : ℝ) ≤ √(12677 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12677 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12677 Θ 1.22 ≤ 0.011777908977 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.592184453451 := by gcongr <;> linarith
      _ ≤ (0.011777908977 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12677 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12677 12677 0.011 ≤ 0.008489816948 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12677 12677 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12677 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12677 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12677 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12677 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162390844543 + 0.011777908977 + (0.008489816948 : ℝ) *
        (1 + 2 * (0.282265819802 + 0.011777908977) / (0.560502526275 * 112.592184453451))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12677]

end BstLean.Part269.N12677

/-! The original eight local profiles supply actual 12677 moment certificates. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12677 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052777435390 ∧
    0 ≤ bN 12677 BstLean.Part154.csC (groupTheta g) ∧ bN 12677 BstLean.Part154.csC (groupTheta g) ≤ 0.001382970974 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12677 12677 0.011
      (momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12677 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12677 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12677 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229733400685 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12677 0.011
      (momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12677 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12677
/-! The actual computed-centre upper energy formula at 12677. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12677

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12677)
open BstLean.Part268 (cell12677)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085557619932
  | 2 => 0.086501613389
  | 3 => 0.087443929041
  | 4 => 0.088386026928
  | 5 => 0.089329671654
  | 6 => 0.090276977433
  | 7 => 0.091230457358
  | 8 => 0.092193076894
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12677 12677 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12677 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12677

/-! Actual upper energy certificates on all 43 source endpoints at 12677. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12677)
open BstLean.Part268 (cell12677)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12677 (gMinus 12677) (1 - (cell12677 i).lower) ≤ 1 ∧
    energyUpper 12677 (gMinus 12677) (BstLean.Part211.gPlus 12677)
      (finiteEnergy 12677 12677 0.011) (1 - (cell12677 i).lower) ≤
      (cell12677 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨10,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨11,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨12,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨13,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨14,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨15,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨16,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨17,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨18,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨19,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨20,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨21,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨22,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨23,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨24,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨25,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨26,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨27,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨28,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨29,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨30,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨31,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨32,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨33,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨34,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨35,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨36,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨37,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨38,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨39,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨40,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨41,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨42,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨43,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨44,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨45,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨46,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨47,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨48,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨49,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨50,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨51,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12677) (by norm_num)
        (q := 1 - (cell12677 ⟨52,by decide⟩).lower)
        (by norm_num [cell12677]) (by norm_num [cell12677])
      exact ⟨E.1,E.2.trans (by norm_num [cell12677])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12677

/-! Source-cell containment and simple scalar guards at 12677. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12677)
open BstLean.Part268 (cell12677)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12677 ⟨10,by decide⟩).lower ∧ (cell12677 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12677 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12677 ⟨11,by decide⟩).lower ∧ (cell12677 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12677 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12677 ⟨12,by decide⟩).lower ∧ (cell12677 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12677 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12677 ⟨13,by decide⟩).lower ∧ (cell12677 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12677 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12677 ⟨14,by decide⟩).lower ∧ (cell12677 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12677 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12677 ⟨15,by decide⟩).lower ∧ (cell12677 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12677 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12677 ⟨16,by decide⟩).lower ∧ (cell12677 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12677 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12677 ⟨17,by decide⟩).lower ∧ (cell12677 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12677 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12677 ⟨18,by decide⟩).lower ∧ (cell12677 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12677 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12677 ⟨19,by decide⟩).lower ∧ (cell12677 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12677 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12677 ⟨20,by decide⟩).lower ∧ (cell12677 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12677 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12677 ⟨21,by decide⟩).lower ∧ (cell12677 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12677 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12677 ⟨22,by decide⟩).lower ∧ (cell12677 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12677 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12677 ⟨23,by decide⟩).lower ∧ (cell12677 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12677 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12677 ⟨24,by decide⟩).lower ∧ (cell12677 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12677 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12677 ⟨25,by decide⟩).lower ∧ (cell12677 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12677 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12677 ⟨26,by decide⟩).lower ∧ (cell12677 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12677 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12677 ⟨27,by decide⟩).lower ∧ (cell12677 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12677 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12677 ⟨28,by decide⟩).lower ∧ (cell12677 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12677 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12677 ⟨29,by decide⟩).lower ∧ (cell12677 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12677 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12677 ⟨30,by decide⟩).lower ∧ (cell12677 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12677 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12677 ⟨31,by decide⟩).lower ∧ (cell12677 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12677 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12677 ⟨32,by decide⟩).lower ∧ (cell12677 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12677 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12677 ⟨33,by decide⟩).lower ∧ (cell12677 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12677 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12677 ⟨34,by decide⟩).lower ∧ (cell12677 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12677 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12677 ⟨35,by decide⟩).lower ∧ (cell12677 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12677 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12677 ⟨36,by decide⟩).lower ∧ (cell12677 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12677 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12677 ⟨37,by decide⟩).lower ∧ (cell12677 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12677 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12677 ⟨38,by decide⟩).lower ∧ (cell12677 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12677 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12677 ⟨39,by decide⟩).lower ∧ (cell12677 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12677 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12677 ⟨40,by decide⟩).lower ∧ (cell12677 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12677 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12677 ⟨41,by decide⟩).lower ∧ (cell12677 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12677 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12677 ⟨42,by decide⟩).lower ∧ (cell12677 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12677 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12677 ⟨43,by decide⟩).lower ∧ (cell12677 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12677 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12677 ⟨44,by decide⟩).lower ∧ (cell12677 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12677 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12677 ⟨45,by decide⟩).lower ∧ (cell12677 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12677 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12677 ⟨46,by decide⟩).lower ∧ (cell12677 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12677 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12677 ⟨47,by decide⟩).lower ∧ (cell12677 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12677 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12677 ⟨48,by decide⟩).lower ∧ (cell12677 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12677 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12677 ⟨49,by decide⟩).lower ∧ (cell12677 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12677 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12677 ⟨50,by decide⟩).lower ∧ (cell12677 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12677 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12677 ⟨51,by decide⟩).lower ∧ (cell12677 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12677 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12677 ⟨52,by decide⟩).lower ∧ (cell12677 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12677 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12677 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12677 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12677,cell12677,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12677 i).lower ∧
    (cell12677 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12677 i).upper ≤ (0.532 : ℝ) ∧
    (cell12677 i).centre ≤ (0.1 : ℝ) ∧ (cell12677 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12677 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12677 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12677

/-! The local source numeric instances at 12677 have no network premises. -/
namespace BstLean.Part269.N12677
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12677)
open BstLean.Part268 (cell12677)

noncomputable def sourceNumerics12677 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12677 (cell12677 i)
      scalarRow12677.M scalarRow12677.H scalarRow12677.xi := by
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
    energy_allowance := scalarRow12677.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12677]
    centre_nonneg := (scalarRow12677.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12677])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12677
/-! Actual 12678 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12678 ≤ (1.035840550615 : ℝ) := by
  have hr : (112.596625171449 : ℝ) ≤ √(12678 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.596625171449 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12678 12678 (11 / 1000) ≤
    (0.008489482114 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12678) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.596625171449 : ℝ) ≤ √(12678 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12678)
  have hdiv : K / √(12678 : ℝ) ≤ K / 112.596625171449 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.596625171449 ≤ (0.008489482114 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12678.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12678 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12678 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12678 := gPlus_lower 12678
end BstLean.Part269.N12678

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12678
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035840550614 : ℝ) ≤ wn 12678 := by
  have hn : √(12678 : ℝ) ≤ 112.596625171450 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12678 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.596625171450 ≤ 2 / √(12678 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252325587 : ℝ) ≤ rhoBar 12678 BstLean.Part154.csC ∧
    rhoBar 12678 BstLean.Part154.csC ≤ 0.000252325978 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035840550614 : ℝ) / (1.295212 * 12678) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035840550615 : ℝ) / (1.29521 * 12678) := by gcongr
      _ ≤ (0.000252325978 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12678 BstLean.Part154.csC) ≤ 0.001009367581 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12678 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) ≤ 0.000192728300 ∧
    cc1 (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) ≤ 0.000122634294 ∧
    cc2 (rhoBar 12678 BstLean.Part154.csC) ≤ 0.000071190143 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12678 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12678 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12678 BstLean.Part154.csC * nuR (rhoBar 12678 BstLean.Part154.csC)) ≤ 0.000504667873 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252325978 : ℝ) * 0.001009367581 := by gcongr
      _ ≤ (0.000504667873 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12678 BstLean.Part154.csC) * nuR (rhoBar 12678 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009367581 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12678 BstLean.Part154.csC) * rhoBar 12678 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252325978 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252325978 / 2 + 0.399 * 0.001009367581 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192728300 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504667873 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122634294 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252325978 / 1.414213562 := by gcongr
      _ ≤ (0.000071190143 : ℝ) := by norm_num

end BstLean.Part269.N12678

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12678
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) ≤ 1.60408E-7 := by
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12678 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12678 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12678 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192728300 : ℝ) ^ 2 + 0.000122634294 ^ 2 + 3 * 0.000071190143 ^ 2 +
        2 * 0.797885 * 0.000192728300 * 0.000122634294 + 2 * 0.000192728300 * 0.000071190143 +
        4 * 0.797885 * 0.000122634294 * 0.000071190143 := by gcongr
    _ ≤ (1.60408E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12678 BstLean.Part154.csC Θ ≤ 0.002634011288 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12678 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12678 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12678 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035840550615 * 1.60408E-7 / (0.000252325587 : ℝ) := by gcongr
    _ ≤ 0.002634011288 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12678 BstLean.Part154.csC Θ ≤ 0.002922665958 + 0.000665572054 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12678 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12678 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035840550615 : ℝ) * ((2 * Θ * 0.000252325978 +
        (6863 / 10000) * 0.000252325978 * 12678 * 0.001009367581) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002922665958 + 0.000665572054 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12678 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12678 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12678 0.011 Θ ∧ gammaRatio 12678 0.011 Θ ≤ 0.000086743146 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12678 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035840550615 : ℝ) * 0.525 / ((1 - 0.011) * 12678) := by gcongr
      _ ≤ (0.000086743146 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12678 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12678 0.011 Θ) :=
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
    badAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12678 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12678 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12678 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12678 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12678 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12678 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12678 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12678 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12678 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12678 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035840550615 : ℝ) * 12678 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538167942 + 0.003299583342 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12678

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12678
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12678 BstLean.Part154.csC) (piBar (rhoBar 12678 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12678 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12678 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12678 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12678 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12678 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12678 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12678 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12678 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12678 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12678 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052530324800 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12678) ≤ 0.010606335486 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12678 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035840550615)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010606335486 + 2 * 0.737676 / 12678) := by gcongr
    _ ≤ (0.052530324800 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12678 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12678

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12678
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502571659 : ℝ) ≤ plow 12678 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12678) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777049197)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382855927) : eMP 12678 0.011 xi bn ≤ 0.001190476816 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12678 : ℝ) * (1 - 0.011))) ≤ 0.000588626634 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382855927 / (12678 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588626634 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588626634 : ℝ) + 3.141593 * 0.052777049197 / (12678 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190476816 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777049197)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382855927) : PiBarMP 12678 12 0.011 xi bn ≤ 0.161392196502 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12678 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037186770861 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.975631277523 : ℝ) ≤ √((12678 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.596625171449 : ℝ) ≤ √(12678 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12678) ≤ 0.123737352177 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037186770861 + 0.052777049197 * 1.772454 / (2 * (111.975631277523 : ℝ))) * (1 + 0.001190476816) +
        8 / (12678 * 112.596625171449) + 0.123737352177 := by gcongr
    _ ≤ (0.161392196502 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777049197)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382855927) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282262884959) :
    parallelOracle 12678 0.011 xi bn cd ≤ 0.162384321192 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12678 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12678 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502571659 : ℝ) ≤ plow 12678 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.596625171449 : ℝ) ≤ √(12678 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282262884959 : ℝ) / (2 * 0.560502571659 * 112.596625171449)) * 0.161392196502 +
        0.282262884959 ^ 2 / (2 * 0.560502571659 * 112.596625171449) := by gcongr
    _ ≤ (0.162384321192 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777049197) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382855927)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282262884959) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12678 12678 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502571659 : ℝ) ≤ plow 12678 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.596625171449 : ℝ) ≤ √(12678 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12678 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12678 Θ 1.22 ≤ 0.011777444466 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.596625171449 := by gcongr <;> linarith
      _ ≤ (0.011777444466 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12678 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12678 12678 0.011 ≤ 0.008489482114 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12678 12678 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12678 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12678 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12678 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12678 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162384321192 + 0.011777444466 + (0.008489482114 : ℝ) *
        (1 + 2 * (0.282262884959 + 0.011777444466) / (0.560502571659 * 112.596625171449))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12678]

end BstLean.Part269.N12678

/-! The original eight local profiles supply actual 12678 moment certificates. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12678 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052777049197 ∧
    0 ≤ bN 12678 BstLean.Part154.csC (groupTheta g) ∧ bN 12678 BstLean.Part154.csC (groupTheta g) ≤ 0.001382855927 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12678 12678 0.011
      (momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12678 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12678 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12678 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229732560159 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12678 0.011
      (momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12678 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12678
/-! The actual computed-centre upper energy formula at 12678. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12678

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12678)
open BstLean.Part268 (cell12678)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085554678968
  | 2 => 0.086498617831
  | 3 => 0.087440870833
  | 4 => 0.088382896168
  | 5 => 0.089326456262
  | 6 => 0.090273662791
  | 7 => 0.091227025900
  | 8 => 0.092189507655
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12678 12678 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12678 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12678

/-! Actual upper energy certificates on all 43 source endpoints at 12678. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12678)
open BstLean.Part268 (cell12678)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12678 (gMinus 12678) (1 - (cell12678 i).lower) ≤ 1 ∧
    energyUpper 12678 (gMinus 12678) (BstLean.Part211.gPlus 12678)
      (finiteEnergy 12678 12678 0.011) (1 - (cell12678 i).lower) ≤
      (cell12678 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨10,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨11,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨12,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨13,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨14,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨15,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨16,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨17,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨18,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨19,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨20,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨21,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨22,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨23,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨24,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨25,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨26,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨27,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨28,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨29,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨30,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨31,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨32,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨33,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨34,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨35,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨36,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨37,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨38,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨39,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨40,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨41,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨42,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨43,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨44,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨45,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨46,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨47,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨48,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨49,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨50,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨51,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12678) (by norm_num)
        (q := 1 - (cell12678 ⟨52,by decide⟩).lower)
        (by norm_num [cell12678]) (by norm_num [cell12678])
      exact ⟨E.1,E.2.trans (by norm_num [cell12678])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12678

/-! Source-cell containment and simple scalar guards at 12678. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12678)
open BstLean.Part268 (cell12678)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12678 ⟨10,by decide⟩).lower ∧ (cell12678 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12678 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12678 ⟨11,by decide⟩).lower ∧ (cell12678 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12678 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12678 ⟨12,by decide⟩).lower ∧ (cell12678 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12678 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12678 ⟨13,by decide⟩).lower ∧ (cell12678 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12678 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12678 ⟨14,by decide⟩).lower ∧ (cell12678 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12678 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12678 ⟨15,by decide⟩).lower ∧ (cell12678 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12678 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12678 ⟨16,by decide⟩).lower ∧ (cell12678 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12678 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12678 ⟨17,by decide⟩).lower ∧ (cell12678 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12678 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12678 ⟨18,by decide⟩).lower ∧ (cell12678 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12678 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12678 ⟨19,by decide⟩).lower ∧ (cell12678 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12678 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12678 ⟨20,by decide⟩).lower ∧ (cell12678 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12678 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12678 ⟨21,by decide⟩).lower ∧ (cell12678 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12678 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12678 ⟨22,by decide⟩).lower ∧ (cell12678 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12678 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12678 ⟨23,by decide⟩).lower ∧ (cell12678 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12678 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12678 ⟨24,by decide⟩).lower ∧ (cell12678 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12678 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12678 ⟨25,by decide⟩).lower ∧ (cell12678 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12678 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12678 ⟨26,by decide⟩).lower ∧ (cell12678 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12678 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12678 ⟨27,by decide⟩).lower ∧ (cell12678 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12678 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12678 ⟨28,by decide⟩).lower ∧ (cell12678 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12678 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12678 ⟨29,by decide⟩).lower ∧ (cell12678 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12678 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12678 ⟨30,by decide⟩).lower ∧ (cell12678 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12678 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12678 ⟨31,by decide⟩).lower ∧ (cell12678 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12678 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12678 ⟨32,by decide⟩).lower ∧ (cell12678 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12678 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12678 ⟨33,by decide⟩).lower ∧ (cell12678 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12678 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12678 ⟨34,by decide⟩).lower ∧ (cell12678 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12678 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12678 ⟨35,by decide⟩).lower ∧ (cell12678 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12678 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12678 ⟨36,by decide⟩).lower ∧ (cell12678 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12678 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12678 ⟨37,by decide⟩).lower ∧ (cell12678 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12678 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12678 ⟨38,by decide⟩).lower ∧ (cell12678 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12678 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12678 ⟨39,by decide⟩).lower ∧ (cell12678 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12678 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12678 ⟨40,by decide⟩).lower ∧ (cell12678 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12678 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12678 ⟨41,by decide⟩).lower ∧ (cell12678 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12678 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12678 ⟨42,by decide⟩).lower ∧ (cell12678 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12678 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12678 ⟨43,by decide⟩).lower ∧ (cell12678 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12678 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12678 ⟨44,by decide⟩).lower ∧ (cell12678 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12678 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12678 ⟨45,by decide⟩).lower ∧ (cell12678 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12678 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12678 ⟨46,by decide⟩).lower ∧ (cell12678 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12678 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12678 ⟨47,by decide⟩).lower ∧ (cell12678 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12678 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12678 ⟨48,by decide⟩).lower ∧ (cell12678 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12678 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12678 ⟨49,by decide⟩).lower ∧ (cell12678 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12678 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12678 ⟨50,by decide⟩).lower ∧ (cell12678 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12678 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12678 ⟨51,by decide⟩).lower ∧ (cell12678 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12678 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12678 ⟨52,by decide⟩).lower ∧ (cell12678 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12678 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12678 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12678 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12678,cell12678,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12678 i).lower ∧
    (cell12678 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12678 i).upper ≤ (0.532 : ℝ) ∧
    (cell12678 i).centre ≤ (0.1 : ℝ) ∧ (cell12678 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12678 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12678 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12678

/-! The local source numeric instances at 12678 have no network premises. -/
namespace BstLean.Part269.N12678
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12678)
open BstLean.Part268 (cell12678)

noncomputable def sourceNumerics12678 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12678 (cell12678 i)
      scalarRow12678.M scalarRow12678.H scalarRow12678.xi := by
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
    energy_allowance := scalarRow12678.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12678]
    centre_nonneg := (scalarRow12678.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12678])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12678
/-! Actual 12679 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12679 ≤ (1.035839124762 : ℝ) := by
  have hr : (112.601065714317 : ℝ) ≤ √(12679 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.601065714317 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12679 12679 (11 / 1000) ≤
    (0.008489147320 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12679) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.601065714317 : ℝ) ≤ √(12679 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12679)
  have hdiv : K / √(12679 : ℝ) ≤ K / 112.601065714317 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.601065714317 ≤ (0.008489147320 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12679.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12679 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12679 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12679 := gPlus_lower 12679
end BstLean.Part269.N12679

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12679
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035839124761 : ℝ) ≤ wn 12679 := by
  have hn : √(12679 : ℝ) ≤ 112.601065714318 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12679 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.601065714318 ≤ 2 / √(12679 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252305339 : ℝ) ≤ rhoBar 12679 BstLean.Part154.csC ∧
    rhoBar 12679 BstLean.Part154.csC ≤ 0.000252305729 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035839124761 : ℝ) / (1.295212 * 12679) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035839124762 : ℝ) / (1.29521 * 12679) := by gcongr
      _ ≤ (0.000252305729 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12679 BstLean.Part154.csC) ≤ 0.001009286575 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12679 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) ≤ 0.000192712833 ∧
    cc1 (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) ≤ 0.000122624452 ∧
    cc2 (rhoBar 12679 BstLean.Part154.csC) ≤ 0.000071184430 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12679 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12679 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12679 BstLean.Part154.csC * nuR (rhoBar 12679 BstLean.Part154.csC)) ≤ 0.000504627373 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252305729 : ℝ) * 0.001009286575 := by gcongr
      _ ≤ (0.000504627373 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12679 BstLean.Part154.csC) * nuR (rhoBar 12679 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009286575 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12679 BstLean.Part154.csC) * rhoBar 12679 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252305729 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252305729 / 2 + 0.399 * 0.001009286575 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192712833 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504627373 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122624452 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252305729 / 1.414213562 := by gcongr
      _ ≤ (0.000071184430 : ℝ) := by norm_num

end BstLean.Part269.N12679

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12679
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) ≤ 1.60382E-7 := by
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12679 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12679 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12679 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192712833 : ℝ) ^ 2 + 0.000122624452 ^ 2 + 3 * 0.000071184430 ^ 2 +
        2 * 0.797885 * 0.000192712833 * 0.000122624452 + 2 * 0.000192712833 * 0.000071184430 +
        4 * 0.797885 * 0.000122624452 * 0.000071184430 := by gcongr
    _ ≤ (1.60382E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12679 BstLean.Part154.csC Θ ≤ 0.002633792074 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12679 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12679 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12679 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035839124762 * 1.60382E-7 / (0.000252305339 : ℝ) := by gcongr
    _ ≤ 0.002633792074 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12679 BstLean.Part154.csC Θ ≤ 0.002922423349 + 0.000665517727 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12679 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12679 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035839124762 : ℝ) * ((2 * Θ * 0.000252305729 +
        (6863 / 10000) * 0.000252305729 * 12679 * 0.001009286575) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002922423349 + 0.000665517727 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12679 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12679 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12679 0.011 Θ ∧ gammaRatio 12679 0.011 Θ ≤ 0.000086736186 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12679 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035839124762 : ℝ) * 0.525 / ((1 - 0.011) * 12679) := by gcongr
      _ ≤ (0.000086736186 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12679 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12679 0.011 Θ) :=
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
    badAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12679 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12679 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12679 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12679 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12679 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12679 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12679 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12679 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12679 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12679 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035839124762 : ℝ) * 12679 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003537925333 + 0.003299309801 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12679

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12679
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12679 BstLean.Part154.csC) (piBar (rhoBar 12679 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12679 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12679 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12679 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12679 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12679 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12679 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12679 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12679 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12679 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12679 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052528230725 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12679) ≤ 0.010605917213 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12679 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035839124762)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010605917213 + 2 * 0.737676 / 12679) := by gcongr
    _ ≤ (0.052528230725 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12679 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12679

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12679
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502617036 : ℝ) ≤ plow 12679 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12679) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776662979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382740839) : eMP 12679 0.011 xi bn ≤ 0.001190380262 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12679 : ℝ) * (1 - 0.011))) ≤ 0.000588578927 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382740839 / (12679 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588578927 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588578927 : ℝ) + 3.141593 * 0.052776662979 / (12679 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190380262 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776662979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382740839) : PiBarMP 12679 12 0.011 xi bn ≤ 0.161385743635 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12679 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037185223396 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.980047329870 : ℝ) ≤ √((12679 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.601065714317 : ℝ) ≤ √(12679 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12679) ≤ 0.123732472463 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037185223396 + 0.052776662979 * 1.772454 / (2 * (111.980047329870 : ℝ))) * (1 + 0.001190380262) +
        8 / (12679 * 112.601065714317) + 0.123732472463 := by gcongr
    _ ≤ (0.161385743635 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776662979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382740839) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282259950301) :
    parallelOracle 12679 0.011 xi bn cd ≤ 0.162377797812 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12679 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12679 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502617036 : ℝ) ≤ plow 12679 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.601065714317 : ℝ) ≤ √(12679 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282259950301 : ℝ) / (2 * 0.560502617036 * 112.601065714317)) * 0.161385743635 +
        0.282259950301 ^ 2 / (2 * 0.560502617036 * 112.601065714317) := by gcongr
    _ ≤ (0.162377797812 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776662979) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382740839)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282259950301) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12679 12679 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502617036 : ℝ) ≤ plow 12679 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.601065714317 : ℝ) ≤ √(12679 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12679 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12679 Θ 1.22 ≤ 0.011776980010 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.601065714317 := by gcongr <;> linarith
      _ ≤ (0.011776980010 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12679 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12679 12679 0.011 ≤ 0.008489147320 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12679 12679 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12679 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12679 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12679 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12679 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162377797812 + 0.011776980010 + (0.008489147320 : ℝ) *
        (1 + 2 * (0.282259950301 + 0.011776980010) / (0.560502617036 * 112.601065714317))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12679]

end BstLean.Part269.N12679

/-! The original eight local profiles supply actual 12679 moment certificates. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12679 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052776662979 ∧
    0 ≤ bN 12679 BstLean.Part154.csC (groupTheta g) ∧ bN 12679 BstLean.Part154.csC (groupTheta g) ≤ 0.001382740839 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12679 12679 0.011
      (momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12679 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12679 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12679 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229731719576 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12679 0.011
      (momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12679 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12679
/-! The actual computed-centre upper energy formula at 12679. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12679

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12679)
open BstLean.Part268 (cell12679)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085551739113
  | 2 => 0.086495623427
  | 3 => 0.087437813836
  | 4 => 0.088379766687
  | 5 => 0.089323242235
  | 6 => 0.090270349618
  | 7 => 0.091223596036
  | 8 => 0.092185940159
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12679 12679 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12679 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12679

/-! Actual upper energy certificates on all 43 source endpoints at 12679. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12679)
open BstLean.Part268 (cell12679)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12679 (gMinus 12679) (1 - (cell12679 i).lower) ≤ 1 ∧
    energyUpper 12679 (gMinus 12679) (BstLean.Part211.gPlus 12679)
      (finiteEnergy 12679 12679 0.011) (1 - (cell12679 i).lower) ≤
      (cell12679 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨10,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨11,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨12,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨13,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨14,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨15,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨16,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨17,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨18,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨19,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨20,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨21,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨22,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨23,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨24,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨25,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨26,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨27,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨28,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨29,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨30,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨31,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨32,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨33,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨34,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨35,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨36,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨37,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨38,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨39,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨40,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨41,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨42,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨43,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨44,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨45,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨46,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨47,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨48,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨49,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨50,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨51,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12679) (by norm_num)
        (q := 1 - (cell12679 ⟨52,by decide⟩).lower)
        (by norm_num [cell12679]) (by norm_num [cell12679])
      exact ⟨E.1,E.2.trans (by norm_num [cell12679])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12679

/-! Source-cell containment and simple scalar guards at 12679. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12679)
open BstLean.Part268 (cell12679)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12679 ⟨10,by decide⟩).lower ∧ (cell12679 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12679 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12679 ⟨11,by decide⟩).lower ∧ (cell12679 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12679 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12679 ⟨12,by decide⟩).lower ∧ (cell12679 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12679 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12679 ⟨13,by decide⟩).lower ∧ (cell12679 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12679 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12679 ⟨14,by decide⟩).lower ∧ (cell12679 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12679 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12679 ⟨15,by decide⟩).lower ∧ (cell12679 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12679 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12679 ⟨16,by decide⟩).lower ∧ (cell12679 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12679 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12679 ⟨17,by decide⟩).lower ∧ (cell12679 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12679 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12679 ⟨18,by decide⟩).lower ∧ (cell12679 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12679 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12679 ⟨19,by decide⟩).lower ∧ (cell12679 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12679 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12679 ⟨20,by decide⟩).lower ∧ (cell12679 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12679 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12679 ⟨21,by decide⟩).lower ∧ (cell12679 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12679 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12679 ⟨22,by decide⟩).lower ∧ (cell12679 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12679 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12679 ⟨23,by decide⟩).lower ∧ (cell12679 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12679 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12679 ⟨24,by decide⟩).lower ∧ (cell12679 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12679 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12679 ⟨25,by decide⟩).lower ∧ (cell12679 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12679 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12679 ⟨26,by decide⟩).lower ∧ (cell12679 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12679 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12679 ⟨27,by decide⟩).lower ∧ (cell12679 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12679 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12679 ⟨28,by decide⟩).lower ∧ (cell12679 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12679 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12679 ⟨29,by decide⟩).lower ∧ (cell12679 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12679 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12679 ⟨30,by decide⟩).lower ∧ (cell12679 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12679 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12679 ⟨31,by decide⟩).lower ∧ (cell12679 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12679 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12679 ⟨32,by decide⟩).lower ∧ (cell12679 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12679 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12679 ⟨33,by decide⟩).lower ∧ (cell12679 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12679 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12679 ⟨34,by decide⟩).lower ∧ (cell12679 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12679 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12679 ⟨35,by decide⟩).lower ∧ (cell12679 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12679 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12679 ⟨36,by decide⟩).lower ∧ (cell12679 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12679 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12679 ⟨37,by decide⟩).lower ∧ (cell12679 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12679 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12679 ⟨38,by decide⟩).lower ∧ (cell12679 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12679 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12679 ⟨39,by decide⟩).lower ∧ (cell12679 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12679 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12679 ⟨40,by decide⟩).lower ∧ (cell12679 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12679 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12679 ⟨41,by decide⟩).lower ∧ (cell12679 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12679 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12679 ⟨42,by decide⟩).lower ∧ (cell12679 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12679 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12679 ⟨43,by decide⟩).lower ∧ (cell12679 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12679 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12679 ⟨44,by decide⟩).lower ∧ (cell12679 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12679 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12679 ⟨45,by decide⟩).lower ∧ (cell12679 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12679 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12679 ⟨46,by decide⟩).lower ∧ (cell12679 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12679 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12679 ⟨47,by decide⟩).lower ∧ (cell12679 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12679 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12679 ⟨48,by decide⟩).lower ∧ (cell12679 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12679 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12679 ⟨49,by decide⟩).lower ∧ (cell12679 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12679 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12679 ⟨50,by decide⟩).lower ∧ (cell12679 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12679 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12679 ⟨51,by decide⟩).lower ∧ (cell12679 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12679 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12679 ⟨52,by decide⟩).lower ∧ (cell12679 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12679 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12679 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12679 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12679,cell12679,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12679 i).lower ∧
    (cell12679 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12679 i).upper ≤ (0.532 : ℝ) ∧
    (cell12679 i).centre ≤ (0.1 : ℝ) ∧ (cell12679 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12679 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12679 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12679

/-! The local source numeric instances at 12679 have no network premises. -/
namespace BstLean.Part269.N12679
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12679)
open BstLean.Part268 (cell12679)

noncomputable def sourceNumerics12679 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12679 (cell12679 i)
      scalarRow12679.M scalarRow12679.H scalarRow12679.xi := by
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
    energy_allowance := scalarRow12679.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12679]
    centre_nonneg := (scalarRow12679.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12679])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12679
/-! Actual 12680 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12680 ≤ (1.035837699080 : ℝ) := by
  have hr : (112.605506082073 : ℝ) ≤ √(12680 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.605506082073 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12680 12680 (11 / 1000) ≤
    (0.008488812565 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12680) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.605506082073 : ℝ) ≤ √(12680 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12680)
  have hdiv : K / √(12680 : ℝ) ≤ K / 112.605506082073 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.605506082073 ≤ (0.008488812565 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12680.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12680 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12680 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12680 := gPlus_lower 12680
end BstLean.Part269.N12680

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12680
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035837699079 : ℝ) ≤ wn 12680 := by
  have hn : √(12680 : ℝ) ≤ 112.605506082074 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12680 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.605506082074 ≤ 2 / √(12680 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252285093 : ℝ) ≤ rhoBar 12680 BstLean.Part154.csC ∧
    rhoBar 12680 BstLean.Part154.csC ≤ 0.000252285484 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035837699079 : ℝ) / (1.295212 * 12680) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035837699080 : ℝ) / (1.29521 * 12680) := by gcongr
      _ ≤ (0.000252285484 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12680 BstLean.Part154.csC) ≤ 0.001009205584 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12680 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) ≤ 0.000192697369 ∧
    cc1 (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) ≤ 0.000122614612 ∧
    cc2 (rhoBar 12680 BstLean.Part154.csC) ≤ 0.000071178718 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12680 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12680 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12680 BstLean.Part154.csC * nuR (rhoBar 12680 BstLean.Part154.csC)) ≤ 0.000504586880 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252285484 : ℝ) * 0.001009205584 := by gcongr
      _ ≤ (0.000504586880 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12680 BstLean.Part154.csC) * nuR (rhoBar 12680 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009205584 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12680 BstLean.Part154.csC) * rhoBar 12680 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252285484 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252285484 / 2 + 0.399 * 0.001009205584 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192697369 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504586880 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122614612 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252285484 / 1.414213562 := by gcongr
      _ ≤ (0.000071178718 : ℝ) := by norm_num

end BstLean.Part269.N12680

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12680
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) ≤ 1.60357E-7 := by
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12680 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12680 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12680 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192697369 : ℝ) ^ 2 + 0.000122614612 ^ 2 + 3 * 0.000071178718 ^ 2 +
        2 * 0.797885 * 0.000192697369 * 0.000122614612 + 2 * 0.000192697369 * 0.000071178718 +
        4 * 0.797885 * 0.000122614612 * 0.000071178718 := by gcongr
    _ ≤ (1.60357E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12680 BstLean.Part154.csC Θ ≤ 0.002633589230 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12680 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12680 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12680 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035837699080 * 1.60357E-7 / (0.000252285093 : ℝ) := by gcongr
    _ ≤ 0.002633589230 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12680 BstLean.Part154.csC Θ ≤ 0.002922180795 + 0.000665463410 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12680 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12680 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035837699080 : ℝ) * ((2 * Θ * 0.000252285484 +
        (6863 / 10000) * 0.000252285484 * 12680 * 0.001009205584) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002922180795 + 0.000665463410 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12680 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12680 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12680 0.011 Θ ∧ gammaRatio 12680 0.011 Θ ≤ 0.000086729226 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12680 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035837699080 : ℝ) * 0.525 / ((1 - 0.011) * 12680) := by gcongr
      _ ≤ (0.000086729226 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12680 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12680 0.011 Θ) :=
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
    badAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12680 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12680 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12680 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12680 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12680 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12680 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12680 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12680 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12680 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12680 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035837699080 : ℝ) * 12680 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003537682779 + 0.003299052640 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12680

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12680
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12680 BstLean.Part154.csC) (piBar (rhoBar 12680 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12680 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12680 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12680 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12680 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12680 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12680 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12680 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12680 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12680 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12680 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052526136906 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12680) ≤ 0.010605498991 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12680 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035837699080)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010605498991 + 2 * 0.737676 / 12680) := by gcongr
    _ ≤ (0.052526136906 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12680 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12680

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12680
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502662405 : ℝ) ≤ plow 12680 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12680) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776285415)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382634346) : eMP 12680 0.011 xi bn ≤ 0.001190287377 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12680 : ℝ) * (1 - 0.011))) ≤ 0.000588533053 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382634346 / (12680 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588533053 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588533053 : ℝ) + 3.141593 * 0.052776285415 / (12680 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190287377 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776285415)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382634346) : PiBarMP 12680 12 0.011 xi bn ≤ 0.161379407202 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12680 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037183791442 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.984463208071 : ℝ) ≤ √((12680 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.605506082073 : ℝ) ≤ √(12680 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12680) ≤ 0.123727593326 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037183791442 + 0.052776285415 * 1.772454 / (2 * (111.984463208071 : ℝ))) * (1 + 0.001190287377) +
        8 / (12680 * 112.605506082073) + 0.123727593326 := by gcongr
    _ ≤ (0.161379407202 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776285415)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382634346) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282257034730) :
    parallelOracle 12680 0.011 xi bn cd ≤ 0.162371391245 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12680 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12680 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502662405 : ℝ) ≤ plow 12680 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.605506082073 : ℝ) ≤ √(12680 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282257034730 : ℝ) / (2 * 0.560502662405 * 112.605506082073)) * 0.161379407202 +
        0.282257034730 ^ 2 / (2 * 0.560502662405 * 112.605506082073) := by gcongr
    _ ≤ (0.162371391245 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052776285415) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382634346)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282257034730) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12680 12680 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502662405 : ℝ) ≤ plow 12680 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.605506082073 : ℝ) ≤ √(12680 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12680 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12680 Θ 1.22 ≤ 0.011776515609 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.605506082073 := by gcongr <;> linarith
      _ ≤ (0.011776515609 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12680 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12680 12680 0.011 ≤ 0.008488812565 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12680 12680 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12680 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12680 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12680 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12680 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162371391245 + 0.011776515609 + (0.008488812565 : ℝ) *
        (1 + 2 * (0.282257034730 + 0.011776515609) / (0.560502662405 * 112.605506082073))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12680]

end BstLean.Part269.N12680

/-! The original eight local profiles supply actual 12680 moment certificates. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12680 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052776285415 ∧
    0 ≤ bN 12680 BstLean.Part154.csC (groupTheta g) ∧ bN 12680 BstLean.Part154.csC (groupTheta g) ≤ 0.001382634346 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12680 12680 0.011
      (momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12680 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12680 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12680 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229730897824 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12680 0.011
      (momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12680 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12680
/-! The actual computed-centre upper energy formula at 12680. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12680

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12680)
open BstLean.Part268 (cell12680)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085548800365
  | 2 => 0.086492630176
  | 3 => 0.087434758049
  | 4 => 0.088376638486
  | 5 => 0.089320029571
  | 6 => 0.090267037912
  | 7 => 0.091220167764
  | 8 => 0.092182374405
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12680 12680 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12680 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12680

/-! Actual upper energy certificates on all 43 source endpoints at 12680. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12680)
open BstLean.Part268 (cell12680)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12680 (gMinus 12680) (1 - (cell12680 i).lower) ≤ 1 ∧
    energyUpper 12680 (gMinus 12680) (BstLean.Part211.gPlus 12680)
      (finiteEnergy 12680 12680 0.011) (1 - (cell12680 i).lower) ≤
      (cell12680 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨10,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨11,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨12,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨13,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨14,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨15,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨16,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨17,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨18,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨19,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨20,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨21,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨22,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨23,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨24,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨25,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨26,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨27,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨28,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨29,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨30,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨31,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨32,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨33,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨34,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨35,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨36,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨37,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨38,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨39,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨40,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨41,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨42,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨43,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨44,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨45,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨46,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨47,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨48,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨49,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨50,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨51,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12680) (by norm_num)
        (q := 1 - (cell12680 ⟨52,by decide⟩).lower)
        (by norm_num [cell12680]) (by norm_num [cell12680])
      exact ⟨E.1,E.2.trans (by norm_num [cell12680])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12680

/-! Source-cell containment and simple scalar guards at 12680. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12680)
open BstLean.Part268 (cell12680)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12680 ⟨10,by decide⟩).lower ∧ (cell12680 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12680 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12680 ⟨11,by decide⟩).lower ∧ (cell12680 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12680 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12680 ⟨12,by decide⟩).lower ∧ (cell12680 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12680 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12680 ⟨13,by decide⟩).lower ∧ (cell12680 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12680 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12680 ⟨14,by decide⟩).lower ∧ (cell12680 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12680 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12680 ⟨15,by decide⟩).lower ∧ (cell12680 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12680 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12680 ⟨16,by decide⟩).lower ∧ (cell12680 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12680 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12680 ⟨17,by decide⟩).lower ∧ (cell12680 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12680 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12680 ⟨18,by decide⟩).lower ∧ (cell12680 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12680 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12680 ⟨19,by decide⟩).lower ∧ (cell12680 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12680 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12680 ⟨20,by decide⟩).lower ∧ (cell12680 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12680 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12680 ⟨21,by decide⟩).lower ∧ (cell12680 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12680 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12680 ⟨22,by decide⟩).lower ∧ (cell12680 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12680 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12680 ⟨23,by decide⟩).lower ∧ (cell12680 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12680 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12680 ⟨24,by decide⟩).lower ∧ (cell12680 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12680 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12680 ⟨25,by decide⟩).lower ∧ (cell12680 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12680 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12680 ⟨26,by decide⟩).lower ∧ (cell12680 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12680 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12680 ⟨27,by decide⟩).lower ∧ (cell12680 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12680 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12680 ⟨28,by decide⟩).lower ∧ (cell12680 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12680 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12680 ⟨29,by decide⟩).lower ∧ (cell12680 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12680 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12680 ⟨30,by decide⟩).lower ∧ (cell12680 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12680 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12680 ⟨31,by decide⟩).lower ∧ (cell12680 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12680 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12680 ⟨32,by decide⟩).lower ∧ (cell12680 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12680 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12680 ⟨33,by decide⟩).lower ∧ (cell12680 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12680 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12680 ⟨34,by decide⟩).lower ∧ (cell12680 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12680 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12680 ⟨35,by decide⟩).lower ∧ (cell12680 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12680 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12680 ⟨36,by decide⟩).lower ∧ (cell12680 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12680 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12680 ⟨37,by decide⟩).lower ∧ (cell12680 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12680 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12680 ⟨38,by decide⟩).lower ∧ (cell12680 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12680 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12680 ⟨39,by decide⟩).lower ∧ (cell12680 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12680 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12680 ⟨40,by decide⟩).lower ∧ (cell12680 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12680 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12680 ⟨41,by decide⟩).lower ∧ (cell12680 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12680 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12680 ⟨42,by decide⟩).lower ∧ (cell12680 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12680 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12680 ⟨43,by decide⟩).lower ∧ (cell12680 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12680 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12680 ⟨44,by decide⟩).lower ∧ (cell12680 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12680 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12680 ⟨45,by decide⟩).lower ∧ (cell12680 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12680 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12680 ⟨46,by decide⟩).lower ∧ (cell12680 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12680 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12680 ⟨47,by decide⟩).lower ∧ (cell12680 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12680 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12680 ⟨48,by decide⟩).lower ∧ (cell12680 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12680 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12680 ⟨49,by decide⟩).lower ∧ (cell12680 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12680 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12680 ⟨50,by decide⟩).lower ∧ (cell12680 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12680 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12680 ⟨51,by decide⟩).lower ∧ (cell12680 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12680 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12680 ⟨52,by decide⟩).lower ∧ (cell12680 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12680 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12680 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12680 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12680,cell12680,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12680 i).lower ∧
    (cell12680 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12680 i).upper ≤ (0.532 : ℝ) ∧
    (cell12680 i).centre ≤ (0.1 : ℝ) ∧ (cell12680 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12680 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12680 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12680

/-! The local source numeric instances at 12680 have no network premises. -/
namespace BstLean.Part269.N12680
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12680)
open BstLean.Part268 (cell12680)

noncomputable def sourceNumerics12680 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12680 (cell12680 i)
      scalarRow12680.M scalarRow12680.H scalarRow12680.xi := by
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
    energy_allowance := scalarRow12680.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12680]
    centre_nonneg := (scalarRow12680.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12680])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12680
/-! Actual 12681 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12681 ≤ (1.035836273567 : ℝ) := by
  have hr : (112.609946274740 : ℝ) ≤ √(12681 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.609946274740 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12681 12681 (11 / 1000) ≤
    (0.008488477850 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12681) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.609946274740 : ℝ) ≤ √(12681 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12681)
  have hdiv : K / √(12681 : ℝ) ≤ K / 112.609946274740 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.609946274740 ≤ (0.008488477850 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12681.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12681 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12681 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12681 := gPlus_lower 12681
end BstLean.Part269.N12681

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12681
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035836273566 : ℝ) ≤ wn 12681 := by
  have hn : √(12681 : ℝ) ≤ 112.609946274741 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12681 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.609946274741 ≤ 2 / √(12681 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252264852 : ℝ) ≤ rhoBar 12681 BstLean.Part154.csC ∧
    rhoBar 12681 BstLean.Part154.csC ≤ 0.000252265242 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035836273566 : ℝ) / (1.295212 * 12681) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035836273567 : ℝ) / (1.29521 * 12681) := by gcongr
      _ ≤ (0.000252265242 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12681 BstLean.Part154.csC) ≤ 0.001009124606 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12681 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) ≤ 0.000192681907 ∧
    cc1 (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) ≤ 0.000122604774 ∧
    cc2 (rhoBar 12681 BstLean.Part154.csC) ≤ 0.000071173007 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12681 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12681 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12681 BstLean.Part154.csC * nuR (rhoBar 12681 BstLean.Part154.csC)) ≤ 0.000504546394 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252265242 : ℝ) * 0.001009124606 := by gcongr
      _ ≤ (0.000504546394 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12681 BstLean.Part154.csC) * nuR (rhoBar 12681 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009124606 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12681 BstLean.Part154.csC) * rhoBar 12681 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252265242 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252265242 / 2 + 0.399 * 0.001009124606 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192681907 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504546394 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122604774 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252265242 / 1.414213562 := by gcongr
      _ ≤ (0.000071173007 : ℝ) := by norm_num

end BstLean.Part269.N12681

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12681
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) ≤ 1.60331E-7 := by
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12681 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12681 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12681 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192681907 : ℝ) ^ 2 + 0.000122604774 ^ 2 + 3 * 0.000071173007 ^ 2 +
        2 * 0.797885 * 0.000192681907 * 0.000122604774 + 2 * 0.000192681907 * 0.000071173007 +
        4 * 0.797885 * 0.000122604774 * 0.000071173007 := by gcongr
    _ ≤ (1.60331E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12681 BstLean.Part154.csC Θ ≤ 0.002633369878 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12681 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12681 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12681 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035836273567 * 1.60331E-7 / (0.000252264852 : ℝ) := by gcongr
    _ ≤ 0.002633369878 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12681 BstLean.Part154.csC Θ ≤ 0.002921938278 + 0.000665409101 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12681 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12681 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035836273567 : ℝ) * ((2 * Θ * 0.000252265242 +
        (6863 / 10000) * 0.000252265242 * 12681 * 0.001009124606) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002921938278 + 0.000665409101 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12681 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12681 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12681 0.011 Θ ∧ gammaRatio 12681 0.011 Θ ≤ 0.000086722267 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12681 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035836273567 : ℝ) * 0.525 / ((1 - 0.011) * 12681) := by gcongr
      _ ≤ (0.000086722267 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12681 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12681 0.011 Θ) :=
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
    badAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12681 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12681 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12681 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12681 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12681 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12681 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12681 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12681 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12681 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12681 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035836273567 : ℝ) * 12681 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003537440262 + 0.003298778979 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12681

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12681
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12681 BstLean.Part154.csC) (piBar (rhoBar 12681 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12681 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12681 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12681 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12681 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12681 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12681 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12681 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12681 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12681 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12681 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052524043335 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12681) ≤ 0.010605080818 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12681 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035836273567)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010605080818 + 2 * 0.737676 / 12681) := by gcongr
    _ ≤ (0.052524043335 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12681 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12681

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12681
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502707767 : ℝ) ≤ plow 12681 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12681) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775899226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382519186) : eMP 12681 0.011 xi bn ≤ 0.001190190808 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12681 : ℝ) * (1 - 0.011))) ≤ 0.000588485338 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382519186 / (12681 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588485338 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588485338 : ℝ) + 3.141593 * 0.052775899226 / (12681 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190190808 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775899226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382519186) : PiBarMP 12681 12 0.011 xi bn ≤ 0.161372954402 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12681 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037182242886 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.988878912149 : ℝ) ≤ √((12681 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.609946274740 : ℝ) ≤ √(12681 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12681) ≤ 0.123722714766 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037182242886 + 0.052775899226 * 1.772454 / (2 * (111.988878912149 : ℝ))) * (1 + 0.001190190808) +
        8 / (12681 * 112.609946274740) + 0.123722714766 := by gcongr
    _ ≤ (0.161372954402 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775899226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382519186) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282254100633) :
    parallelOracle 12681 0.011 xi bn cd ≤ 0.162364867951 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12681 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12681 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502707767 : ℝ) ≤ plow 12681 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.609946274740 : ℝ) ≤ √(12681 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282254100633 : ℝ) / (2 * 0.560502707767 * 112.609946274740)) * 0.161372954402 +
        0.282254100633 ^ 2 / (2 * 0.560502707767 * 112.609946274740) := by gcongr
    _ ≤ (0.162364867951 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775899226) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382519186)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282254100633) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12681 12681 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502707767 : ℝ) ≤ plow 12681 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.609946274740 : ℝ) ≤ √(12681 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12681 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12681 Θ 1.22 ≤ 0.011776051263 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.609946274740 := by gcongr <;> linarith
      _ ≤ (0.011776051263 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12681 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12681 12681 0.011 ≤ 0.008488477850 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12681 12681 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12681 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12681 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12681 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12681 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162364867951 + 0.011776051263 + (0.008488477850 : ℝ) *
        (1 + 2 * (0.282254100633 + 0.011776051263) / (0.560502707767 * 112.609946274740))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12681]

end BstLean.Part269.N12681

/-! The original eight local profiles supply actual 12681 moment certificates. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12681 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052775899226 ∧
    0 ≤ bN 12681 BstLean.Part154.csC (groupTheta g) ∧ bN 12681 BstLean.Part154.csC (groupTheta g) ≤ 0.001382519186 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12681 12681 0.011
      (momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12681 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12681 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12681 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229730057298 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12681 0.011
      (momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12681 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12681
/-! The actual computed-centre upper energy formula at 12681. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12681

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12681)
open BstLean.Part268 (cell12681)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085545862723
  | 2 => 0.086489638077
  | 3 => 0.087431703470
  | 4 => 0.088373511561
  | 5 => 0.089316818270
  | 6 => 0.090263727670
  | 7 => 0.091216741081
  | 8 => 0.092178810390
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12681 12681 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12681 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12681

/-! Actual upper energy certificates on all 43 source endpoints at 12681. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12681)
open BstLean.Part268 (cell12681)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12681 (gMinus 12681) (1 - (cell12681 i).lower) ≤ 1 ∧
    energyUpper 12681 (gMinus 12681) (BstLean.Part211.gPlus 12681)
      (finiteEnergy 12681 12681 0.011) (1 - (cell12681 i).lower) ≤
      (cell12681 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨10,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨11,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨12,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨13,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨14,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨15,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨16,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨17,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨18,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨19,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨20,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨21,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨22,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨23,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨24,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨25,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨26,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨27,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨28,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨29,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨30,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨31,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨32,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨33,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨34,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨35,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨36,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨37,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨38,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨39,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨40,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨41,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨42,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨43,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨44,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨45,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨46,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨47,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨48,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨49,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨50,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨51,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12681) (by norm_num)
        (q := 1 - (cell12681 ⟨52,by decide⟩).lower)
        (by norm_num [cell12681]) (by norm_num [cell12681])
      exact ⟨E.1,E.2.trans (by norm_num [cell12681])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12681

/-! Source-cell containment and simple scalar guards at 12681. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12681)
open BstLean.Part268 (cell12681)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12681 ⟨10,by decide⟩).lower ∧ (cell12681 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12681 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12681 ⟨11,by decide⟩).lower ∧ (cell12681 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12681 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12681 ⟨12,by decide⟩).lower ∧ (cell12681 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12681 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12681 ⟨13,by decide⟩).lower ∧ (cell12681 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12681 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12681 ⟨14,by decide⟩).lower ∧ (cell12681 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12681 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12681 ⟨15,by decide⟩).lower ∧ (cell12681 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12681 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12681 ⟨16,by decide⟩).lower ∧ (cell12681 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12681 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12681 ⟨17,by decide⟩).lower ∧ (cell12681 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12681 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12681 ⟨18,by decide⟩).lower ∧ (cell12681 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12681 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12681 ⟨19,by decide⟩).lower ∧ (cell12681 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12681 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12681 ⟨20,by decide⟩).lower ∧ (cell12681 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12681 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12681 ⟨21,by decide⟩).lower ∧ (cell12681 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12681 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12681 ⟨22,by decide⟩).lower ∧ (cell12681 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12681 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12681 ⟨23,by decide⟩).lower ∧ (cell12681 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12681 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12681 ⟨24,by decide⟩).lower ∧ (cell12681 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12681 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12681 ⟨25,by decide⟩).lower ∧ (cell12681 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12681 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12681 ⟨26,by decide⟩).lower ∧ (cell12681 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12681 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12681 ⟨27,by decide⟩).lower ∧ (cell12681 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12681 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12681 ⟨28,by decide⟩).lower ∧ (cell12681 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12681 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12681 ⟨29,by decide⟩).lower ∧ (cell12681 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12681 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12681 ⟨30,by decide⟩).lower ∧ (cell12681 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12681 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12681 ⟨31,by decide⟩).lower ∧ (cell12681 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12681 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12681 ⟨32,by decide⟩).lower ∧ (cell12681 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12681 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12681 ⟨33,by decide⟩).lower ∧ (cell12681 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12681 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12681 ⟨34,by decide⟩).lower ∧ (cell12681 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12681 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12681 ⟨35,by decide⟩).lower ∧ (cell12681 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12681 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12681 ⟨36,by decide⟩).lower ∧ (cell12681 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12681 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12681 ⟨37,by decide⟩).lower ∧ (cell12681 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12681 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12681 ⟨38,by decide⟩).lower ∧ (cell12681 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12681 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12681 ⟨39,by decide⟩).lower ∧ (cell12681 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12681 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12681 ⟨40,by decide⟩).lower ∧ (cell12681 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12681 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12681 ⟨41,by decide⟩).lower ∧ (cell12681 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12681 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12681 ⟨42,by decide⟩).lower ∧ (cell12681 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12681 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12681 ⟨43,by decide⟩).lower ∧ (cell12681 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12681 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12681 ⟨44,by decide⟩).lower ∧ (cell12681 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12681 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12681 ⟨45,by decide⟩).lower ∧ (cell12681 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12681 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12681 ⟨46,by decide⟩).lower ∧ (cell12681 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12681 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12681 ⟨47,by decide⟩).lower ∧ (cell12681 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12681 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12681 ⟨48,by decide⟩).lower ∧ (cell12681 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12681 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12681 ⟨49,by decide⟩).lower ∧ (cell12681 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12681 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12681 ⟨50,by decide⟩).lower ∧ (cell12681 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12681 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12681 ⟨51,by decide⟩).lower ∧ (cell12681 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12681 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12681 ⟨52,by decide⟩).lower ∧ (cell12681 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12681 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12681 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12681 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12681,cell12681,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12681 i).lower ∧
    (cell12681 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12681 i).upper ≤ (0.532 : ℝ) ∧
    (cell12681 i).centre ≤ (0.1 : ℝ) ∧ (cell12681 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12681 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12681 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12681

/-! The local source numeric instances at 12681 have no network premises. -/
namespace BstLean.Part269.N12681
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12681)
open BstLean.Part268 (cell12681)

noncomputable def sourceNumerics12681 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12681 (cell12681 i)
      scalarRow12681.M scalarRow12681.H scalarRow12681.xi := by
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
    energy_allowance := scalarRow12681.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12681]
    centre_nonneg := (scalarRow12681.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12681])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12681
/-! Actual 12682 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12682 ≤ (1.035834848224 : ℝ) := by
  have hr : (112.614386292338 : ℝ) ≤ √(12682 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.614386292338 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12682 12682 (11 / 1000) ≤
    (0.008488143174 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12682) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.614386292338 : ℝ) ≤ √(12682 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12682)
  have hdiv : K / √(12682 : ℝ) ≤ K / 112.614386292338 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.614386292338 ≤ (0.008488143174 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12682.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12682 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12682 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12682 := gPlus_lower 12682
end BstLean.Part269.N12682

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12682
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035834848223 : ℝ) ≤ wn 12682 := by
  have hn : √(12682 : ℝ) ≤ 112.614386292339 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12682 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.614386292339 ≤ 2 / √(12682 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252244613 : ℝ) ≤ rhoBar 12682 BstLean.Part154.csC ∧
    rhoBar 12682 BstLean.Part154.csC ≤ 0.000252245003 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035834848223 : ℝ) / (1.295212 * 12682) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035834848224 : ℝ) / (1.29521 * 12682) := by gcongr
      _ ≤ (0.000252245003 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12682 BstLean.Part154.csC) ≤ 0.001009043640 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12682 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) ≤ 0.000192666448 ∧
    cc1 (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) ≤ 0.000122594937 ∧
    cc2 (rhoBar 12682 BstLean.Part154.csC) ≤ 0.000071167297 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12682 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12682 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12682 BstLean.Part154.csC * nuR (rhoBar 12682 BstLean.Part154.csC)) ≤ 0.000504505913 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252245003 : ℝ) * 0.001009043640 := by gcongr
      _ ≤ (0.000504505913 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12682 BstLean.Part154.csC) * nuR (rhoBar 12682 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009043640 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12682 BstLean.Part154.csC) * rhoBar 12682 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252245003 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252245003 / 2 + 0.399 * 0.001009043640 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192666448 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504505913 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122594937 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252245003 / 1.414213562 := by gcongr
      _ ≤ (0.000071167297 : ℝ) := by norm_num

end BstLean.Part269.N12682

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12682
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) ≤ 1.60305E-7 := by
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12682 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12682 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12682 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192666448 : ℝ) ^ 2 + 0.000122594937 ^ 2 + 3 * 0.000071167297 ^ 2 +
        2 * 0.797885 * 0.000192666448 * 0.000122594937 + 2 * 0.000192666448 * 0.000071167297 +
        4 * 0.797885 * 0.000122594937 * 0.000071167297 := by gcongr
    _ ≤ (1.60305E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12682 BstLean.Part154.csC Θ ≤ 0.002633150471 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12682 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12682 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12682 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035834848224 * 1.60305E-7 / (0.000252244613 : ℝ) := by gcongr
    _ ≤ 0.002633150471 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12682 BstLean.Part154.csC Θ ≤ 0.002921695795 + 0.000665354800 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12682 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12682 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035834848224 : ℝ) * ((2 * Θ * 0.000252245003 +
        (6863 / 10000) * 0.000252245003 * 12682 * 0.001009043640) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002921695795 + 0.000665354800 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12682 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12682 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12682 0.011 Θ ∧ gammaRatio 12682 0.011 Θ ≤ 0.000086715310 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12682 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035834848224 : ℝ) * 0.525 / ((1 - 0.011) * 12682) := by gcongr
      _ ≤ (0.000086715310 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12682 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12682 0.011 Θ) :=
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
    badAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12682 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12682 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12682 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12682 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12682 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12682 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12682 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12682 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12682 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12682 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035834848224 : ℝ) * 12682 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003537197779 + 0.003298505271 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12682

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12682
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12682 BstLean.Part154.csC) (piBar (rhoBar 12682 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12682 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12682 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12682 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12682 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12682 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12682 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12682 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12682 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12682 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12682 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052521950012 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12682) ≤ 0.010604662694 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12682 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035834848224)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010604662694 + 2 * 0.737676 / 12682) := by gcongr
    _ ≤ (0.052521950012 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12682 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12682

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12682
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502753122 : ℝ) ≤ plow 12682 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12682) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775513047)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382403998) : eMP 12682 0.011 xi bn ≤ 0.001190094235 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12682 : ℝ) * (1 - 0.011))) ≤ 0.000588437621 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382403998 / (12682 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588437621 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588437621 : ℝ) + 3.141593 * 0.052775513047 / (12682 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190094235 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775513047)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382403998) : PiBarMP 12682 12 0.011 xi bn ≤ 0.161366501740 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12682 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037180693889 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.993294442122 : ℝ) ≤ √((12682 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.614386292338 : ℝ) ≤ √(12682 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12682) ≤ 0.123717836784 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037180693889 + 0.052775513047 * 1.772454 / (2 * (111.993294442122 : ℝ))) * (1 + 0.001190094235) +
        8 / (12682 * 112.614386292338) + 0.123717836784 := by gcongr
    _ ≤ (0.161366501740 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775513047)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382403998) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282251166803) :
    parallelOracle 12682 0.011 xi bn cd ≤ 0.162358344805 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12682 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12682 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502753122 : ℝ) ≤ plow 12682 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.614386292338 : ℝ) ≤ √(12682 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282251166803 : ℝ) / (2 * 0.560502753122 * 112.614386292338)) * 0.161366501740 +
        0.282251166803 ^ 2 / (2 * 0.560502753122 * 112.614386292338) := by gcongr
    _ ≤ (0.162358344805 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775513047) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382403998)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282251166803) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12682 12682 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502753122 : ℝ) ≤ plow 12682 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.614386292338 : ℝ) ≤ √(12682 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12682 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12682 Θ 1.22 ≤ 0.011775586972 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.614386292338 := by gcongr <;> linarith
      _ ≤ (0.011775586972 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12682 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12682 12682 0.011 ≤ 0.008488143174 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12682 12682 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12682 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12682 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12682 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12682 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162358344805 + 0.011775586972 + (0.008488143174 : ℝ) *
        (1 + 2 * (0.282251166803 + 0.011775586972) / (0.560502753122 * 112.614386292338))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12682]

end BstLean.Part269.N12682

/-! The original eight local profiles supply actual 12682 moment certificates. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12682 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052775513047 ∧
    0 ≤ bN 12682 BstLean.Part154.csC (groupTheta g) ∧ bN 12682 BstLean.Part154.csC (groupTheta g) ≤ 0.001382403998 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12682 12682 0.011
      (momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12682 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12682 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12682 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229729216791 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12682 0.011
      (momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12682 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12682
/-! The actual computed-centre upper energy formula at 12682. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12682

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12682)
open BstLean.Part268 (cell12682)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085542926186
  | 2 => 0.086486647128
  | 3 => 0.087428650098
  | 4 => 0.088370385914
  | 5 => 0.089313608330
  | 6 => 0.090260418893
  | 7 => 0.091213315986
  | 8 => 0.092175248113
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12682 12682 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12682 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12682

/-! Actual upper energy certificates on all 43 source endpoints at 12682. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12682)
open BstLean.Part268 (cell12682)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12682 (gMinus 12682) (1 - (cell12682 i).lower) ≤ 1 ∧
    energyUpper 12682 (gMinus 12682) (BstLean.Part211.gPlus 12682)
      (finiteEnergy 12682 12682 0.011) (1 - (cell12682 i).lower) ≤
      (cell12682 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨10,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨11,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨12,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨13,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨14,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨15,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨16,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨17,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨18,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨19,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨20,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨21,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨22,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨23,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨24,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨25,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨26,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨27,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨28,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨29,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨30,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨31,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨32,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨33,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨34,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨35,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨36,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨37,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨38,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨39,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨40,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨41,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨42,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨43,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨44,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨45,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨46,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨47,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨48,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨49,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨50,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨51,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12682) (by norm_num)
        (q := 1 - (cell12682 ⟨52,by decide⟩).lower)
        (by norm_num [cell12682]) (by norm_num [cell12682])
      exact ⟨E.1,E.2.trans (by norm_num [cell12682])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12682

/-! Source-cell containment and simple scalar guards at 12682. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12682)
open BstLean.Part268 (cell12682)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12682 ⟨10,by decide⟩).lower ∧ (cell12682 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12682 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12682 ⟨11,by decide⟩).lower ∧ (cell12682 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12682 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12682 ⟨12,by decide⟩).lower ∧ (cell12682 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12682 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12682 ⟨13,by decide⟩).lower ∧ (cell12682 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12682 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12682 ⟨14,by decide⟩).lower ∧ (cell12682 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12682 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12682 ⟨15,by decide⟩).lower ∧ (cell12682 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12682 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12682 ⟨16,by decide⟩).lower ∧ (cell12682 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12682 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12682 ⟨17,by decide⟩).lower ∧ (cell12682 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12682 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12682 ⟨18,by decide⟩).lower ∧ (cell12682 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12682 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12682 ⟨19,by decide⟩).lower ∧ (cell12682 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12682 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12682 ⟨20,by decide⟩).lower ∧ (cell12682 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12682 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12682 ⟨21,by decide⟩).lower ∧ (cell12682 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12682 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12682 ⟨22,by decide⟩).lower ∧ (cell12682 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12682 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12682 ⟨23,by decide⟩).lower ∧ (cell12682 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12682 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12682 ⟨24,by decide⟩).lower ∧ (cell12682 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12682 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12682 ⟨25,by decide⟩).lower ∧ (cell12682 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12682 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12682 ⟨26,by decide⟩).lower ∧ (cell12682 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12682 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12682 ⟨27,by decide⟩).lower ∧ (cell12682 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12682 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12682 ⟨28,by decide⟩).lower ∧ (cell12682 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12682 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12682 ⟨29,by decide⟩).lower ∧ (cell12682 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12682 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12682 ⟨30,by decide⟩).lower ∧ (cell12682 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12682 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12682 ⟨31,by decide⟩).lower ∧ (cell12682 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12682 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12682 ⟨32,by decide⟩).lower ∧ (cell12682 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12682 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12682 ⟨33,by decide⟩).lower ∧ (cell12682 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12682 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12682 ⟨34,by decide⟩).lower ∧ (cell12682 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12682 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12682 ⟨35,by decide⟩).lower ∧ (cell12682 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12682 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12682 ⟨36,by decide⟩).lower ∧ (cell12682 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12682 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12682 ⟨37,by decide⟩).lower ∧ (cell12682 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12682 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12682 ⟨38,by decide⟩).lower ∧ (cell12682 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12682 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12682 ⟨39,by decide⟩).lower ∧ (cell12682 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12682 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12682 ⟨40,by decide⟩).lower ∧ (cell12682 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12682 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12682 ⟨41,by decide⟩).lower ∧ (cell12682 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12682 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12682 ⟨42,by decide⟩).lower ∧ (cell12682 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12682 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12682 ⟨43,by decide⟩).lower ∧ (cell12682 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12682 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12682 ⟨44,by decide⟩).lower ∧ (cell12682 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12682 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12682 ⟨45,by decide⟩).lower ∧ (cell12682 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12682 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12682 ⟨46,by decide⟩).lower ∧ (cell12682 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12682 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12682 ⟨47,by decide⟩).lower ∧ (cell12682 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12682 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12682 ⟨48,by decide⟩).lower ∧ (cell12682 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12682 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12682 ⟨49,by decide⟩).lower ∧ (cell12682 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12682 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12682 ⟨50,by decide⟩).lower ∧ (cell12682 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12682 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12682 ⟨51,by decide⟩).lower ∧ (cell12682 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12682 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12682 ⟨52,by decide⟩).lower ∧ (cell12682 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12682 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12682 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12682 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12682,cell12682,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12682 i).lower ∧
    (cell12682 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12682 i).upper ≤ (0.532 : ℝ) ∧
    (cell12682 i).centre ≤ (0.1 : ℝ) ∧ (cell12682 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12682 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12682 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12682

/-! The local source numeric instances at 12682 have no network premises. -/
namespace BstLean.Part269.N12682
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12682)
open BstLean.Part268 (cell12682)

noncomputable def sourceNumerics12682 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12682 (cell12682 i)
      scalarRow12682.M scalarRow12682.H scalarRow12682.xi := by
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
    energy_allowance := scalarRow12682.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12682]
    centre_nonneg := (scalarRow12682.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12682])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12682
/-! Actual 12683 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12683 ≤ (1.035833423050 : ℝ) := by
  have hr : (112.618826134887 : ℝ) ≤ √(12683 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.618826134887 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12683 12683 (11 / 1000) ≤
    (0.008487808538 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12683) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.618826134887 : ℝ) ≤ √(12683 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12683)
  have hdiv : K / √(12683 : ℝ) ≤ K / 112.618826134887 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.618826134887 ≤ (0.008487808538 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12683.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12683 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12683 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12683 := gPlus_lower 12683
end BstLean.Part269.N12683

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12683
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035833423049 : ℝ) ≤ wn 12683 := by
  have hn : √(12683 : ℝ) ≤ 112.618826134888 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12683 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.618826134888 ≤ 2 / √(12683 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252224377 : ℝ) ≤ rhoBar 12683 BstLean.Part154.csC ∧
    rhoBar 12683 BstLean.Part154.csC ≤ 0.000252224768 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035833423049 : ℝ) / (1.295212 * 12683) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035833423050 : ℝ) / (1.29521 * 12683) := by gcongr
      _ ≤ (0.000252224768 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12683 BstLean.Part154.csC) ≤ 0.001008962690 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12683 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) ≤ 0.000192650992 ∧
    cc1 (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) ≤ 0.000122585103 ∧
    cc2 (rhoBar 12683 BstLean.Part154.csC) ≤ 0.000071161588 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12683 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12683 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12683 BstLean.Part154.csC * nuR (rhoBar 12683 BstLean.Part154.csC)) ≤ 0.000504465441 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252224768 : ℝ) * 0.001008962690 := by gcongr
      _ ≤ (0.000504465441 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12683 BstLean.Part154.csC) * nuR (rhoBar 12683 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008962690 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12683 BstLean.Part154.csC) * rhoBar 12683 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252224768 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252224768 / 2 + 0.399 * 0.001008962690 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192650992 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504465441 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122585103 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252224768 / 1.414213562 := by gcongr
      _ ≤ (0.000071161588 : ℝ) := by norm_num

end BstLean.Part269.N12683

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12683
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) ≤ 1.60279E-7 := by
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12683 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12683 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12683 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192650992 : ℝ) ^ 2 + 0.000122585103 ^ 2 + 3 * 0.000071161588 ^ 2 +
        2 * 0.797885 * 0.000192650992 * 0.000122585103 + 2 * 0.000192650992 * 0.000071161588 +
        4 * 0.797885 * 0.000122585103 * 0.000071161588 := by gcongr
    _ ≤ (1.60279E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12683 BstLean.Part154.csC Θ ≤ 0.002632930999 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12683 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12683 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12683 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035833423050 * 1.60279E-7 / (0.000252224377 : ℝ) := by gcongr
    _ ≤ 0.002632930999 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12683 BstLean.Part154.csC Θ ≤ 0.002921453370 + 0.000665300510 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12683 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12683 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035833423050 : ℝ) * ((2 * Θ * 0.000252224768 +
        (6863 / 10000) * 0.000252224768 * 12683 * 0.001008962690) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002921453370 + 0.000665300510 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12683 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12683 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12683 0.011 Θ ∧ gammaRatio 12683 0.011 Θ ≤ 0.000086708353 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12683 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035833423050 : ℝ) * 0.525 / ((1 - 0.011) * 12683) := by gcongr
      _ ≤ (0.000086708353 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12683 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12683 0.011 Θ) :=
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
    badAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12683 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12683 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12683 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12683 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12683 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12683 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12683 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12683 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12683 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12683 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035833423050 : ℝ) * 12683 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003536955354 + 0.003298231509 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12683

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12683
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12683 BstLean.Part154.csC) (piBar (rhoBar 12683 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12683 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12683 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12683 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12683 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12683 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12683 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12683 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12683 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12683 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12683 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052519856940 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12683) ≤ 0.010604244620 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12683 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035833423050)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010604244620 + 2 * 0.737676 / 12683) := by gcongr
    _ ≤ (0.052519856940 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12683 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12683

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12683
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502798470 : ℝ) ≤ plow 12683 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12683) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775126897)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382288775) : eMP 12683 0.011 xi bn ≤ 0.001189997654 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12683 : ℝ) * (1 - 0.011))) ≤ 0.000588389900 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382288775 / (12683 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588389900 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588389900 : ℝ) + 3.141593 * 0.052775126897 / (12683 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189997654 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775126897)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382288775) : PiBarMP 12683 12 0.011 xi bn ≤ 0.161360049120 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12683 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037179144356 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.997709798013 : ℝ) ≤ √((12683 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.618826134887 : ℝ) ≤ √(12683 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12683) ≤ 0.123712959378 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037179144356 + 0.052775126897 * 1.772454 / (2 * (111.997709798013 : ℝ))) * (1 + 0.001189997654) +
        8 / (12683 * 112.618826134887) + 0.123712959378 := by gcongr
    _ ≤ (0.161360049120 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775126897)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382288775) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282248233283) :
    parallelOracle 12683 0.011 xi bn cd ≤ 0.162351821710 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12683 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12683 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502798470 : ℝ) ≤ plow 12683 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.618826134887 : ℝ) ≤ √(12683 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282248233283 : ℝ) / (2 * 0.560502798470 * 112.618826134887)) * 0.161360049120 +
        0.282248233283 ^ 2 / (2 * 0.560502798470 * 112.618826134887) := by gcongr
    _ ≤ (0.162351821710 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052775126897) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382288775)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282248233283) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12683 12683 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502798470 : ℝ) ≤ plow 12683 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.618826134887 : ℝ) ≤ √(12683 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12683 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12683 Θ 1.22 ≤ 0.011775122735 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.618826134887 := by gcongr <;> linarith
      _ ≤ (0.011775122735 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12683 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12683 12683 0.011 ≤ 0.008487808538 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12683 12683 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12683 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12683 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12683 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12683 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162351821710 + 0.011775122735 + (0.008487808538 : ℝ) *
        (1 + 2 * (0.282248233283 + 0.011775122735) / (0.560502798470 * 112.618826134887))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12683]

end BstLean.Part269.N12683

/-! The original eight local profiles supply actual 12683 moment certificates. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12683 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052775126897 ∧
    0 ≤ bN 12683 BstLean.Part154.csC (groupTheta g) ∧ bN 12683 BstLean.Part154.csC (groupTheta g) ≤ 0.001382288775 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12683 12683 0.011
      (momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12683 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12683 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12683 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229728376343 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12683 0.011
      (momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12683 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12683
/-! The actual computed-centre upper energy formula at 12683. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12683

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12683)
open BstLean.Part268 (cell12683)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085539990753
  | 2 => 0.086483657329
  | 3 => 0.087425597932
  | 4 => 0.088367261541
  | 5 => 0.089310399749
  | 6 => 0.090257111577
  | 7 => 0.091209892478
  | 8 => 0.092171687572
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12683 12683 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12683 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12683

/-! Actual upper energy certificates on all 43 source endpoints at 12683. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12683)
open BstLean.Part268 (cell12683)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12683 (gMinus 12683) (1 - (cell12683 i).lower) ≤ 1 ∧
    energyUpper 12683 (gMinus 12683) (BstLean.Part211.gPlus 12683)
      (finiteEnergy 12683 12683 0.011) (1 - (cell12683 i).lower) ≤
      (cell12683 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨10,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨11,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨12,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨13,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨14,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨15,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨16,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨17,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨18,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨19,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨20,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨21,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨22,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨23,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨24,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨25,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨26,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨27,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨28,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨29,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨30,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨31,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨32,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨33,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨34,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨35,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨36,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨37,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨38,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨39,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨40,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨41,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨42,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨43,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨44,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨45,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨46,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨47,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨48,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨49,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨50,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨51,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12683) (by norm_num)
        (q := 1 - (cell12683 ⟨52,by decide⟩).lower)
        (by norm_num [cell12683]) (by norm_num [cell12683])
      exact ⟨E.1,E.2.trans (by norm_num [cell12683])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12683

/-! Source-cell containment and simple scalar guards at 12683. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12683)
open BstLean.Part268 (cell12683)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12683 ⟨10,by decide⟩).lower ∧ (cell12683 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12683 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12683 ⟨11,by decide⟩).lower ∧ (cell12683 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12683 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12683 ⟨12,by decide⟩).lower ∧ (cell12683 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12683 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12683 ⟨13,by decide⟩).lower ∧ (cell12683 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12683 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12683 ⟨14,by decide⟩).lower ∧ (cell12683 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12683 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12683 ⟨15,by decide⟩).lower ∧ (cell12683 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12683 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12683 ⟨16,by decide⟩).lower ∧ (cell12683 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12683 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12683 ⟨17,by decide⟩).lower ∧ (cell12683 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12683 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12683 ⟨18,by decide⟩).lower ∧ (cell12683 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12683 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12683 ⟨19,by decide⟩).lower ∧ (cell12683 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12683 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12683 ⟨20,by decide⟩).lower ∧ (cell12683 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12683 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12683 ⟨21,by decide⟩).lower ∧ (cell12683 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12683 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12683 ⟨22,by decide⟩).lower ∧ (cell12683 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12683 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12683 ⟨23,by decide⟩).lower ∧ (cell12683 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12683 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12683 ⟨24,by decide⟩).lower ∧ (cell12683 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12683 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12683 ⟨25,by decide⟩).lower ∧ (cell12683 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12683 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12683 ⟨26,by decide⟩).lower ∧ (cell12683 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12683 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12683 ⟨27,by decide⟩).lower ∧ (cell12683 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12683 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12683 ⟨28,by decide⟩).lower ∧ (cell12683 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12683 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12683 ⟨29,by decide⟩).lower ∧ (cell12683 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12683 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12683 ⟨30,by decide⟩).lower ∧ (cell12683 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12683 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12683 ⟨31,by decide⟩).lower ∧ (cell12683 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12683 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12683 ⟨32,by decide⟩).lower ∧ (cell12683 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12683 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12683 ⟨33,by decide⟩).lower ∧ (cell12683 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12683 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12683 ⟨34,by decide⟩).lower ∧ (cell12683 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12683 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12683 ⟨35,by decide⟩).lower ∧ (cell12683 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12683 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12683 ⟨36,by decide⟩).lower ∧ (cell12683 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12683 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12683 ⟨37,by decide⟩).lower ∧ (cell12683 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12683 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12683 ⟨38,by decide⟩).lower ∧ (cell12683 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12683 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12683 ⟨39,by decide⟩).lower ∧ (cell12683 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12683 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12683 ⟨40,by decide⟩).lower ∧ (cell12683 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12683 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12683 ⟨41,by decide⟩).lower ∧ (cell12683 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12683 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12683 ⟨42,by decide⟩).lower ∧ (cell12683 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12683 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12683 ⟨43,by decide⟩).lower ∧ (cell12683 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12683 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12683 ⟨44,by decide⟩).lower ∧ (cell12683 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12683 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12683 ⟨45,by decide⟩).lower ∧ (cell12683 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12683 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12683 ⟨46,by decide⟩).lower ∧ (cell12683 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12683 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12683 ⟨47,by decide⟩).lower ∧ (cell12683 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12683 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12683 ⟨48,by decide⟩).lower ∧ (cell12683 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12683 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12683 ⟨49,by decide⟩).lower ∧ (cell12683 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12683 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12683 ⟨50,by decide⟩).lower ∧ (cell12683 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12683 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12683 ⟨51,by decide⟩).lower ∧ (cell12683 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12683 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12683 ⟨52,by decide⟩).lower ∧ (cell12683 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12683 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12683 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12683 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12683,cell12683,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12683 i).lower ∧
    (cell12683 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12683 i).upper ≤ (0.532 : ℝ) ∧
    (cell12683 i).centre ≤ (0.1 : ℝ) ∧ (cell12683 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12683 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12683 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12683

/-! The local source numeric instances at 12683 have no network premises. -/
namespace BstLean.Part269.N12683
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12683)
open BstLean.Part268 (cell12683)

noncomputable def sourceNumerics12683 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12683 (cell12683 i)
      scalarRow12683.M scalarRow12683.H scalarRow12683.xi := by
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
    energy_allowance := scalarRow12683.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12683]
    centre_nonneg := (scalarRow12683.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12683])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12683
/-! Actual 12684 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12684 ≤ (1.035831998046 : ℝ) := by
  have hr : (112.623265802408 : ℝ) ≤ √(12684 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.623265802408 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12684 12684 (11 / 1000) ≤
    (0.008487473942 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12684) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.623265802408 : ℝ) ≤ √(12684 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12684)
  have hdiv : K / √(12684 : ℝ) ≤ K / 112.623265802408 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.623265802408 ≤ (0.008487473942 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12684.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12684 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12684 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12684 := gPlus_lower 12684
end BstLean.Part269.N12684

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12684
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035831998045 : ℝ) ≤ wn 12684 := by
  have hn : √(12684 : ℝ) ≤ 112.623265802409 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12684 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.623265802409 ≤ 2 / √(12684 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252204145 : ℝ) ≤ rhoBar 12684 BstLean.Part154.csC ∧
    rhoBar 12684 BstLean.Part154.csC ≤ 0.000252204536 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035831998045 : ℝ) / (1.295212 * 12684) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035831998046 : ℝ) / (1.29521 * 12684) := by gcongr
      _ ≤ (0.000252204536 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12684 BstLean.Part154.csC) ≤ 0.001008881752 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12684 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) ≤ 0.000192635538 ∧
    cc1 (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) ≤ 0.000122575269 ∧
    cc2 (rhoBar 12684 BstLean.Part154.csC) ≤ 0.000071155880 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12684 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12684 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12684 BstLean.Part154.csC * nuR (rhoBar 12684 BstLean.Part154.csC)) ≤ 0.000504424974 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252204536 : ℝ) * 0.001008881752 := by gcongr
      _ ≤ (0.000504424974 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12684 BstLean.Part154.csC) * nuR (rhoBar 12684 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008881752 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12684 BstLean.Part154.csC) * rhoBar 12684 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252204536 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252204536 / 2 + 0.399 * 0.001008881752 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192635538 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504424974 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122575269 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252204536 / 1.414213562 := by gcongr
      _ ≤ (0.000071155880 : ℝ) := by norm_num

end BstLean.Part269.N12684

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12684
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) ≤ 1.60254E-7 := by
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12684 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12684 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12684 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192635538 : ℝ) ^ 2 + 0.000122575269 ^ 2 + 3 * 0.000071155880 ^ 2 +
        2 * 0.797885 * 0.000192635538 * 0.000122575269 + 2 * 0.000192635538 * 0.000071155880 +
        4 * 0.797885 * 0.000122575269 * 0.000071155880 := by gcongr
    _ ≤ (1.60254E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12684 BstLean.Part154.csC Θ ≤ 0.002632727881 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12684 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12684 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12684 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035831998046 * 1.60254E-7 / (0.000252204145 : ℝ) := by gcongr
    _ ≤ 0.002632727881 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12684 BstLean.Part154.csC Θ ≤ 0.002921210979 + 0.000665246228 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12684 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12684 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035831998046 : ℝ) * ((2 * Θ * 0.000252204536 +
        (6863 / 10000) * 0.000252204536 * 12684 * 0.001008881752) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002921210979 + 0.000665246228 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12684 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12684 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12684 0.011 Θ ∧ gammaRatio 12684 0.011 Θ ≤ 0.000086701398 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12684 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035831998046 : ℝ) * 0.525 / ((1 - 0.011) * 12684) := by gcongr
      _ ≤ (0.000086701398 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12684 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12684 0.011 Θ) :=
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
    badAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12684 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12684 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12684 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12684 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12684 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12684 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12684 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12684 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12684 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12684 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035831998046 : ℝ) * 12684 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003536712963 + 0.003297974109 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12684

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12684
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12684 BstLean.Part154.csC) (piBar (rhoBar 12684 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12684 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12684 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12684 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12684 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12684 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12684 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12684 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12684 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12684 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12684 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052517764115 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12684) ≤ 0.010603826595 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12684 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035831998046)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010603826595 + 2 * 0.737676 / 12684) := by gcongr
    _ ≤ (0.052517764115 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12684 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12684

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12684
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502843811 : ℝ) ≤ plow 12684 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12684) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774749371)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382182138) : eMP 12684 0.011 xi bn ≤ 0.001189904737 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12684 : ℝ) * (1 - 0.011))) ≤ 0.000588344010 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382182138 / (12684 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588344010 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588344010 : ℝ) + 3.141593 * 0.052774749371 / (12684 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189904737 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774749371)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382182138) : PiBarMP 12684 12 0.011 xi bn ≤ 0.161353712831 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12684 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037177710231 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.002124979841 : ℝ) ≤ √((12684 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.623265802408 : ℝ) ≤ √(12684 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12684) ≤ 0.123708082549 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037177710231 + 0.052774749371 * 1.772454 / (2 * (112.002124979841 : ℝ))) * (1 + 0.001189904737) +
        8 / (12684 * 112.623265802408) + 0.123708082549 := by gcongr
    _ ≤ (0.161353712831 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774749371)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382182138) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282245318778) :
    parallelOracle 12684 0.011 xi bn cd ≤ 0.162345415323 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12684 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12684 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502843811 : ℝ) ≤ plow 12684 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.623265802408 : ℝ) ≤ √(12684 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282245318778 : ℝ) / (2 * 0.560502843811 * 112.623265802408)) * 0.161353712831 +
        0.282245318778 ^ 2 / (2 * 0.560502843811 * 112.623265802408) := by gcongr
    _ ≤ (0.162345415323 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774749371) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382182138)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282245318778) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12684 12684 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502843811 : ℝ) ≤ plow 12684 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.623265802408 : ℝ) ≤ √(12684 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12684 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12684 Θ 1.22 ≤ 0.011774658554 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.623265802408 := by gcongr <;> linarith
      _ ≤ (0.011774658554 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12684 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12684 12684 0.011 ≤ 0.008487473942 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12684 12684 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12684 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12684 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12684 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12684 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162345415323 + 0.011774658554 + (0.008487473942 : ℝ) *
        (1 + 2 * (0.282245318778 + 0.011774658554) / (0.560502843811 * 112.623265802408))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12684]

end BstLean.Part269.N12684

/-! The original eight local profiles supply actual 12684 moment certificates. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12684 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052774749371 ∧
    0 ≤ bN 12684 BstLean.Part154.csC (groupTheta g) ∧ bN 12684 BstLean.Part154.csC (groupTheta g) ≤ 0.001382182138 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12684 12684 0.011
      (momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12684 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12684 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12684 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229727554663 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12684 0.011
      (momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12684 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12684
/-! The actual computed-centre upper energy formula at 12684. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12684

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12684)
open BstLean.Part268 (cell12684)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085537056423
  | 2 => 0.086480668678
  | 3 => 0.087422546970
  | 4 => 0.088364138441
  | 5 => 0.089307192526
  | 6 => 0.090253805722
  | 7 => 0.091206470554
  | 8 => 0.092168128764
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12684 12684 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12684 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12684

/-! Actual upper energy certificates on all 43 source endpoints at 12684. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12684)
open BstLean.Part268 (cell12684)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12684 (gMinus 12684) (1 - (cell12684 i).lower) ≤ 1 ∧
    energyUpper 12684 (gMinus 12684) (BstLean.Part211.gPlus 12684)
      (finiteEnergy 12684 12684 0.011) (1 - (cell12684 i).lower) ≤
      (cell12684 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨10,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨11,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨12,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨13,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨14,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨15,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨16,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨17,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨18,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨19,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨20,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨21,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨22,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨23,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨24,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨25,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨26,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨27,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨28,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨29,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨30,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨31,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨32,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨33,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨34,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨35,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨36,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨37,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨38,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨39,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨40,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨41,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨42,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨43,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨44,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨45,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨46,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨47,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨48,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨49,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨50,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨51,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12684) (by norm_num)
        (q := 1 - (cell12684 ⟨52,by decide⟩).lower)
        (by norm_num [cell12684]) (by norm_num [cell12684])
      exact ⟨E.1,E.2.trans (by norm_num [cell12684])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12684

/-! Source-cell containment and simple scalar guards at 12684. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12684)
open BstLean.Part268 (cell12684)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12684 ⟨10,by decide⟩).lower ∧ (cell12684 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12684 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12684 ⟨11,by decide⟩).lower ∧ (cell12684 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12684 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12684 ⟨12,by decide⟩).lower ∧ (cell12684 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12684 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12684 ⟨13,by decide⟩).lower ∧ (cell12684 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12684 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12684 ⟨14,by decide⟩).lower ∧ (cell12684 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12684 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12684 ⟨15,by decide⟩).lower ∧ (cell12684 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12684 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12684 ⟨16,by decide⟩).lower ∧ (cell12684 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12684 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12684 ⟨17,by decide⟩).lower ∧ (cell12684 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12684 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12684 ⟨18,by decide⟩).lower ∧ (cell12684 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12684 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12684 ⟨19,by decide⟩).lower ∧ (cell12684 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12684 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12684 ⟨20,by decide⟩).lower ∧ (cell12684 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12684 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12684 ⟨21,by decide⟩).lower ∧ (cell12684 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12684 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12684 ⟨22,by decide⟩).lower ∧ (cell12684 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12684 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12684 ⟨23,by decide⟩).lower ∧ (cell12684 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12684 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12684 ⟨24,by decide⟩).lower ∧ (cell12684 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12684 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12684 ⟨25,by decide⟩).lower ∧ (cell12684 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12684 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12684 ⟨26,by decide⟩).lower ∧ (cell12684 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12684 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12684 ⟨27,by decide⟩).lower ∧ (cell12684 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12684 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12684 ⟨28,by decide⟩).lower ∧ (cell12684 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12684 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12684 ⟨29,by decide⟩).lower ∧ (cell12684 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12684 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12684 ⟨30,by decide⟩).lower ∧ (cell12684 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12684 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12684 ⟨31,by decide⟩).lower ∧ (cell12684 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12684 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12684 ⟨32,by decide⟩).lower ∧ (cell12684 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12684 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12684 ⟨33,by decide⟩).lower ∧ (cell12684 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12684 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12684 ⟨34,by decide⟩).lower ∧ (cell12684 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12684 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12684 ⟨35,by decide⟩).lower ∧ (cell12684 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12684 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12684 ⟨36,by decide⟩).lower ∧ (cell12684 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12684 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12684 ⟨37,by decide⟩).lower ∧ (cell12684 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12684 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12684 ⟨38,by decide⟩).lower ∧ (cell12684 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12684 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12684 ⟨39,by decide⟩).lower ∧ (cell12684 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12684 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12684 ⟨40,by decide⟩).lower ∧ (cell12684 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12684 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12684 ⟨41,by decide⟩).lower ∧ (cell12684 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12684 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12684 ⟨42,by decide⟩).lower ∧ (cell12684 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12684 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12684 ⟨43,by decide⟩).lower ∧ (cell12684 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12684 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12684 ⟨44,by decide⟩).lower ∧ (cell12684 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12684 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12684 ⟨45,by decide⟩).lower ∧ (cell12684 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12684 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12684 ⟨46,by decide⟩).lower ∧ (cell12684 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12684 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12684 ⟨47,by decide⟩).lower ∧ (cell12684 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12684 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12684 ⟨48,by decide⟩).lower ∧ (cell12684 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12684 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12684 ⟨49,by decide⟩).lower ∧ (cell12684 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12684 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12684 ⟨50,by decide⟩).lower ∧ (cell12684 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12684 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12684 ⟨51,by decide⟩).lower ∧ (cell12684 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12684 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12684 ⟨52,by decide⟩).lower ∧ (cell12684 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12684 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12684 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12684 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12684,cell12684,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12684 i).lower ∧
    (cell12684 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12684 i).upper ≤ (0.532 : ℝ) ∧
    (cell12684 i).centre ≤ (0.1 : ℝ) ∧ (cell12684 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12684 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12684 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12684

/-! The local source numeric instances at 12684 have no network premises. -/
namespace BstLean.Part269.N12684
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12684)
open BstLean.Part268 (cell12684)

noncomputable def sourceNumerics12684 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12684 (cell12684 i)
      scalarRow12684.M scalarRow12684.H scalarRow12684.xi := by
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
    energy_allowance := scalarRow12684.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12684]
    centre_nonneg := (scalarRow12684.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12684])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12684
/-! Actual 12685 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12685 ≤ (1.035830573211 : ℝ) := by
  have hr : (112.627705294922 : ℝ) ≤ √(12685 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.627705294922 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12685 12685 (11 / 1000) ≤
    (0.008487139385 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12685) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.627705294922 : ℝ) ≤ √(12685 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12685)
  have hdiv : K / √(12685 : ℝ) ≤ K / 112.627705294922 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.627705294922 ≤ (0.008487139385 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12685.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12685 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12685 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12685 := gPlus_lower 12685
end BstLean.Part269.N12685

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12685
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035830573210 : ℝ) ≤ wn 12685 := by
  have hn : √(12685 : ℝ) ≤ 112.627705294923 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12685 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.627705294923 ≤ 2 / √(12685 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252183916 : ℝ) ≤ rhoBar 12685 BstLean.Part154.csC ∧
    rhoBar 12685 BstLean.Part154.csC ≤ 0.000252184307 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035830573210 : ℝ) / (1.295212 * 12685) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035830573211 : ℝ) / (1.29521 * 12685) := by gcongr
      _ ≤ (0.000252184307 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12685 BstLean.Part154.csC) ≤ 0.001008800825 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12685 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) ≤ 0.000192620086 ∧
    cc1 (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) ≤ 0.000122565437 ∧
    cc2 (rhoBar 12685 BstLean.Part154.csC) ≤ 0.000071150173 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12685 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12685 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12685 BstLean.Part154.csC * nuR (rhoBar 12685 BstLean.Part154.csC)) ≤ 0.000504384513 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252184307 : ℝ) * 0.001008800825 := by gcongr
      _ ≤ (0.000504384513 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12685 BstLean.Part154.csC) * nuR (rhoBar 12685 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008800825 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12685 BstLean.Part154.csC) * rhoBar 12685 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252184307 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252184307 / 2 + 0.399 * 0.001008800825 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192620086 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504384513 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122565437 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252184307 / 1.414213562 := by gcongr
      _ ≤ (0.000071150173 : ℝ) := by norm_num

end BstLean.Part269.N12685

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12685
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) ≤ 1.60228E-7 := by
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12685 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12685 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12685 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192620086 : ℝ) ^ 2 + 0.000122565437 ^ 2 + 3 * 0.000071150173 ^ 2 +
        2 * 0.797885 * 0.000192620086 * 0.000122565437 + 2 * 0.000192620086 * 0.000071150173 +
        4 * 0.797885 * 0.000122565437 * 0.000071150173 := by gcongr
    _ ≤ (1.60228E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12685 BstLean.Part154.csC Θ ≤ 0.002632508270 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12685 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12685 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12685 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035830573211 * 1.60228E-7 / (0.000252183916 : ℝ) := by gcongr
    _ ≤ 0.002632508270 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12685 BstLean.Part154.csC Θ ≤ 0.002920968619 + 0.000665191955 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12685 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12685 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035830573211 : ℝ) * ((2 * Θ * 0.000252184307 +
        (6863 / 10000) * 0.000252184307 * 12685 * 0.001008800825) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002920968619 + 0.000665191955 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12685 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12685 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12685 0.011 Θ ∧ gammaRatio 12685 0.011 Θ ≤ 0.000086694444 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12685 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035830573211 : ℝ) * 0.525 / ((1 - 0.011) * 12685) := by gcongr
      _ ≤ (0.000086694444 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12685 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12685 0.011 Θ) :=
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
    badAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12685 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12685 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12685 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12685 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12685 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12685 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12685 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12685 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12685 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12685 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035830573211 : ℝ) * 12685 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003536470603 + 0.003297700225 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12685

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12685
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12685 BstLean.Part154.csC) (piBar (rhoBar 12685 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12685 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12685 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12685 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12685 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12685 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12685 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12685 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12685 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12685 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12685 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052515671537 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12685) ≤ 0.010603408619 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12685 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035830573211)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010603408619 + 2 * 0.737676 / 12685) := by gcongr
    _ ≤ (0.052515671537 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12685 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12685

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12685
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502889144 : ℝ) ≤ plow 12685 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12685) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774363222)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382066842) : eMP 12685 0.011 xi bn ≤ 0.001189808140 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12685 : ℝ) * (1 - 0.011))) ≤ 0.000588296281 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001382066842 / (12685 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588296281 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588296281 : ℝ) + 3.141593 * 0.052774363222 / (12685 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189808140 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774363222)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382066842) : PiBarMP 12685 12 0.011 xi bn ≤ 0.161347260263 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12685 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037176159592 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.006539987627 : ℝ) ≤ √((12685 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.627705294922 : ℝ) ≤ √(12685 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12685) ≤ 0.123703206297 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037176159592 + 0.052774363222 * 1.772454 / (2 * (112.006539987627 : ℝ))) * (1 + 0.001189808140) +
        8 / (12685 * 112.627705294922) + 0.123703206297 := by gcongr
    _ ≤ (0.161347260263 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774363222)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382066842) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282242385748) :
    parallelOracle 12685 0.011 xi bn cd ≤ 0.162338892298 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12685 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12685 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502889144 : ℝ) ≤ plow 12685 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.627705294922 : ℝ) ≤ √(12685 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282242385748 : ℝ) / (2 * 0.560502889144 * 112.627705294922)) * 0.161347260263 +
        0.282242385748 ^ 2 / (2 * 0.560502889144 * 112.627705294922) := by gcongr
    _ ≤ (0.162338892298 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052774363222) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001382066842)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282242385748) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12685 12685 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502889144 : ℝ) ≤ plow 12685 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.627705294922 : ℝ) ≤ √(12685 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12685 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12685 Θ 1.22 ≤ 0.011774194427 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.627705294922 := by gcongr <;> linarith
      _ ≤ (0.011774194427 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12685 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12685 12685 0.011 ≤ 0.008487139385 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12685 12685 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12685 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12685 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12685 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12685 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162338892298 + 0.011774194427 + (0.008487139385 : ℝ) *
        (1 + 2 * (0.282242385748 + 0.011774194427) / (0.560502889144 * 112.627705294922))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12685]

end BstLean.Part269.N12685

/-! The original eight local profiles supply actual 12685 moment certificates. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12685 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052774363222 ∧
    0 ≤ bN 12685 BstLean.Part154.csC (groupTheta g) ∧ bN 12685 BstLean.Part154.csC (groupTheta g) ≤ 0.001382066842 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12685 12685 0.011
      (momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12685 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12685 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12685 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229726714211 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12685 0.011
      (momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12685 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12685
/-! The actual computed-centre upper energy formula at 12685. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12685

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12685)
open BstLean.Part268 (cell12685)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085534123194
  | 2 => 0.086477681175
  | 3 => 0.087419497211
  | 4 => 0.088361016614
  | 5 => 0.089303986659
  | 6 => 0.090250501326
  | 7 => 0.091203050213
  | 8 => 0.092164571688
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12685 12685 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12685 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12685

/-! Actual upper energy certificates on all 43 source endpoints at 12685. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12685)
open BstLean.Part268 (cell12685)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12685 (gMinus 12685) (1 - (cell12685 i).lower) ≤ 1 ∧
    energyUpper 12685 (gMinus 12685) (BstLean.Part211.gPlus 12685)
      (finiteEnergy 12685 12685 0.011) (1 - (cell12685 i).lower) ≤
      (cell12685 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨10,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨11,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨12,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨13,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨14,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨15,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨16,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨17,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨18,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨19,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨20,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨21,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨22,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨23,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨24,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨25,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨26,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨27,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨28,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨29,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨30,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨31,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨32,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨33,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨34,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨35,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨36,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨37,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨38,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨39,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨40,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨41,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨42,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨43,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨44,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨45,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨46,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨47,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨48,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨49,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨50,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨51,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12685) (by norm_num)
        (q := 1 - (cell12685 ⟨52,by decide⟩).lower)
        (by norm_num [cell12685]) (by norm_num [cell12685])
      exact ⟨E.1,E.2.trans (by norm_num [cell12685])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12685

/-! Source-cell containment and simple scalar guards at 12685. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12685)
open BstLean.Part268 (cell12685)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12685 ⟨10,by decide⟩).lower ∧ (cell12685 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12685 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12685 ⟨11,by decide⟩).lower ∧ (cell12685 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12685 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12685 ⟨12,by decide⟩).lower ∧ (cell12685 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12685 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12685 ⟨13,by decide⟩).lower ∧ (cell12685 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12685 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12685 ⟨14,by decide⟩).lower ∧ (cell12685 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12685 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12685 ⟨15,by decide⟩).lower ∧ (cell12685 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12685 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12685 ⟨16,by decide⟩).lower ∧ (cell12685 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12685 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12685 ⟨17,by decide⟩).lower ∧ (cell12685 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12685 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12685 ⟨18,by decide⟩).lower ∧ (cell12685 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12685 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12685 ⟨19,by decide⟩).lower ∧ (cell12685 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12685 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12685 ⟨20,by decide⟩).lower ∧ (cell12685 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12685 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12685 ⟨21,by decide⟩).lower ∧ (cell12685 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12685 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12685 ⟨22,by decide⟩).lower ∧ (cell12685 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12685 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12685 ⟨23,by decide⟩).lower ∧ (cell12685 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12685 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12685 ⟨24,by decide⟩).lower ∧ (cell12685 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12685 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12685 ⟨25,by decide⟩).lower ∧ (cell12685 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12685 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12685 ⟨26,by decide⟩).lower ∧ (cell12685 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12685 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12685 ⟨27,by decide⟩).lower ∧ (cell12685 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12685 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12685 ⟨28,by decide⟩).lower ∧ (cell12685 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12685 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12685 ⟨29,by decide⟩).lower ∧ (cell12685 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12685 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12685 ⟨30,by decide⟩).lower ∧ (cell12685 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12685 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12685 ⟨31,by decide⟩).lower ∧ (cell12685 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12685 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12685 ⟨32,by decide⟩).lower ∧ (cell12685 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12685 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12685 ⟨33,by decide⟩).lower ∧ (cell12685 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12685 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12685 ⟨34,by decide⟩).lower ∧ (cell12685 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12685 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12685 ⟨35,by decide⟩).lower ∧ (cell12685 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12685 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12685 ⟨36,by decide⟩).lower ∧ (cell12685 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12685 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12685 ⟨37,by decide⟩).lower ∧ (cell12685 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12685 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12685 ⟨38,by decide⟩).lower ∧ (cell12685 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12685 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12685 ⟨39,by decide⟩).lower ∧ (cell12685 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12685 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12685 ⟨40,by decide⟩).lower ∧ (cell12685 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12685 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12685 ⟨41,by decide⟩).lower ∧ (cell12685 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12685 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12685 ⟨42,by decide⟩).lower ∧ (cell12685 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12685 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12685 ⟨43,by decide⟩).lower ∧ (cell12685 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12685 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12685 ⟨44,by decide⟩).lower ∧ (cell12685 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12685 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12685 ⟨45,by decide⟩).lower ∧ (cell12685 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12685 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12685 ⟨46,by decide⟩).lower ∧ (cell12685 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12685 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12685 ⟨47,by decide⟩).lower ∧ (cell12685 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12685 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12685 ⟨48,by decide⟩).lower ∧ (cell12685 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12685 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12685 ⟨49,by decide⟩).lower ∧ (cell12685 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12685 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12685 ⟨50,by decide⟩).lower ∧ (cell12685 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12685 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12685 ⟨51,by decide⟩).lower ∧ (cell12685 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12685 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12685 ⟨52,by decide⟩).lower ∧ (cell12685 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12685 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12685 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12685 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12685,cell12685,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12685 i).lower ∧
    (cell12685 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12685 i).upper ≤ (0.532 : ℝ) ∧
    (cell12685 i).centre ≤ (0.1 : ℝ) ∧ (cell12685 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12685 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12685 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12685

/-! The local source numeric instances at 12685 have no network premises. -/
namespace BstLean.Part269.N12685
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12685)
open BstLean.Part268 (cell12685)

noncomputable def sourceNumerics12685 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12685 (cell12685 i)
      scalarRow12685.M scalarRow12685.H scalarRow12685.xi := by
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
    energy_allowance := scalarRow12685.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12685]
    centre_nonneg := (scalarRow12685.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12685])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12685
/-! Actual 12686 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12686 ≤ (1.035829148546 : ℝ) := by
  have hr : (112.632144612450 : ℝ) ≤ √(12686 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.632144612450 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12686 12686 (11 / 1000) ≤
    (0.008486804868 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12686) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.632144612450 : ℝ) ≤ √(12686 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12686)
  have hdiv : K / √(12686 : ℝ) ≤ K / 112.632144612450 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.632144612450 ≤ (0.008486804868 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12686.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12686 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12686 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12686 := gPlus_lower 12686
end BstLean.Part269.N12686

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12686
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035829148545 : ℝ) ≤ wn 12686 := by
  have hn : √(12686 : ℝ) ≤ 112.632144612451 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12686 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.632144612451 ≤ 2 / √(12686 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252163691 : ℝ) ≤ rhoBar 12686 BstLean.Part154.csC ∧
    rhoBar 12686 BstLean.Part154.csC ≤ 0.000252164081 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035829148545 : ℝ) / (1.295212 * 12686) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035829148546 : ℝ) / (1.29521 * 12686) := by gcongr
      _ ≤ (0.000252164081 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12686 BstLean.Part154.csC) ≤ 0.001008719911 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12686 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) ≤ 0.000192604636 ∧
    cc1 (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) ≤ 0.000122555607 ∧
    cc2 (rhoBar 12686 BstLean.Part154.csC) ≤ 0.000071144466 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12686 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12686 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12686 BstLean.Part154.csC * nuR (rhoBar 12686 BstLean.Part154.csC)) ≤ 0.000504344059 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252164081 : ℝ) * 0.001008719911 := by gcongr
      _ ≤ (0.000504344059 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12686 BstLean.Part154.csC) * nuR (rhoBar 12686 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008719911 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12686 BstLean.Part154.csC) * rhoBar 12686 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252164081 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252164081 / 2 + 0.399 * 0.001008719911 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192604636 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504344059 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122555607 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252164081 / 1.414213562 := by gcongr
      _ ≤ (0.000071144466 : ℝ) := by norm_num

end BstLean.Part269.N12686

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12686
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) ≤ 1.60202E-7 := by
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12686 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12686 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12686 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192604636 : ℝ) ^ 2 + 0.000122555607 ^ 2 + 3 * 0.000071144466 ^ 2 +
        2 * 0.797885 * 0.000192604636 * 0.000122555607 + 2 * 0.000192604636 * 0.000071144466 +
        4 * 0.797885 * 0.000122555607 * 0.000071144466 := by gcongr
    _ ≤ (1.60202E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12686 BstLean.Part154.csC Θ ≤ 0.002632288584 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12686 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12686 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12686 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035829148546 * 1.60202E-7 / (0.000252163691 : ℝ) := by gcongr
    _ ≤ 0.002632288584 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12686 BstLean.Part154.csC Θ ≤ 0.002920726297 + 0.000665137689 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12686 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12686 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035829148546 : ℝ) * ((2 * Θ * 0.000252164081 +
        (6863 / 10000) * 0.000252164081 * 12686 * 0.001008719911) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002920726297 + 0.000665137689 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12686 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12686 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12686 0.011 Θ ∧ gammaRatio 12686 0.011 Θ ≤ 0.000086687491 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12686 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035829148546 : ℝ) * 0.525 / ((1 - 0.011) * 12686) := by gcongr
      _ ≤ (0.000086687491 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12686 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12686 0.011 Θ) :=
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
    badAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12686 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12686 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12686 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12686 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12686 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12686 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12686 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12686 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12686 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12686 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035829148546 : ℝ) * 12686 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003536228281 + 0.003297426273 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12686

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12686
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12686 BstLean.Part154.csC) (piBar (rhoBar 12686 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12686 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12686 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12686 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12686 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12686 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12686 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12686 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12686 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12686 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12686 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052513579212 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12686) ≤ 0.010602990693 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12686 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035829148546)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010602990693 + 2 * 0.737676 / 12686) := by gcongr
    _ ≤ (0.052513579212 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12686 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12686

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12686
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502934471 : ℝ) ≤ plow 12686 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12686) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773977075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381951507) : eMP 12686 0.011 xi bn ≤ 0.001189711534 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12686 : ℝ) * (1 - 0.011))) ≤ 0.000588248547 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381951507 / (12686 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588248547 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588248547 : ℝ) + 3.141593 * 0.052773977075 / (12686 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189711534 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773977075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381951507) : PiBarMP 12686 12 0.011 xi bn ≤ 0.161340807683 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12686 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037174608364 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.010954821392 : ℝ) ≤ √((12686 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.632144612450 : ℝ) ≤ √(12686 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12686) ≤ 0.123698330621 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037174608364 + 0.052773977075 * 1.772454 / (2 * (112.010954821392 : ℝ))) * (1 + 0.001189711534) +
        8 / (12686 * 112.632144612450) + 0.123698330621 := by gcongr
    _ ≤ (0.161340807683 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773977075)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381951507) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282239452973) :
    parallelOracle 12686 0.011 xi bn cd ≤ 0.162332369270 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12686 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12686 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502934471 : ℝ) ≤ plow 12686 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.632144612450 : ℝ) ≤ √(12686 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282239452973 : ℝ) / (2 * 0.560502934471 * 112.632144612450)) * 0.161340807683 +
        0.282239452973 ^ 2 / (2 * 0.560502934471 * 112.632144612450) := by gcongr
    _ ≤ (0.162332369270 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773977075) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381951507)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282239452973) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12686 12686 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502934471 : ℝ) ≤ plow 12686 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.632144612450 : ℝ) ≤ √(12686 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12686 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12686 Θ 1.22 ≤ 0.011773730356 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.632144612450 := by gcongr <;> linarith
      _ ≤ (0.011773730356 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12686 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12686 12686 0.011 ≤ 0.008486804868 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12686 12686 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12686 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12686 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12686 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12686 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162332369270 + 0.011773730356 + (0.008486804868 : ℝ) *
        (1 + 2 * (0.282239452973 + 0.011773730356) / (0.560502934471 * 112.632144612450))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12686]

end BstLean.Part269.N12686

/-! The original eight local profiles supply actual 12686 moment certificates. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12686 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052773977075 ∧
    0 ≤ bN 12686 BstLean.Part154.csC (groupTheta g) ∧ bN 12686 BstLean.Part154.csC (groupTheta g) ≤ 0.001381951507 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12686 12686 0.011
      (momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12686 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12686 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12686 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229725873761 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12686 0.011
      (momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12686 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12686
/-! The actual computed-centre upper energy formula at 12686. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12686

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12686)
open BstLean.Part268 (cell12686)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085531191066
  | 2 => 0.086474694817
  | 3 => 0.087416448654
  | 4 => 0.088357896057
  | 5 => 0.089300782148
  | 6 => 0.090247198387
  | 7 => 0.091199631453
  | 8 => 0.092161016342
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12686 12686 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12686 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12686

/-! Actual upper energy certificates on all 43 source endpoints at 12686. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12686)
open BstLean.Part268 (cell12686)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12686 (gMinus 12686) (1 - (cell12686 i).lower) ≤ 1 ∧
    energyUpper 12686 (gMinus 12686) (BstLean.Part211.gPlus 12686)
      (finiteEnergy 12686 12686 0.011) (1 - (cell12686 i).lower) ≤
      (cell12686 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨10,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨11,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨12,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨13,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨14,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨15,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨16,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨17,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨18,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨19,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨20,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨21,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨22,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨23,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨24,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨25,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨26,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨27,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨28,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨29,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨30,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨31,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨32,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨33,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨34,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨35,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨36,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨37,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨38,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨39,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨40,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨41,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨42,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨43,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨44,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨45,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨46,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨47,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨48,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨49,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨50,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨51,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12686) (by norm_num)
        (q := 1 - (cell12686 ⟨52,by decide⟩).lower)
        (by norm_num [cell12686]) (by norm_num [cell12686])
      exact ⟨E.1,E.2.trans (by norm_num [cell12686])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12686

/-! Source-cell containment and simple scalar guards at 12686. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12686)
open BstLean.Part268 (cell12686)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12686 ⟨10,by decide⟩).lower ∧ (cell12686 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12686 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12686 ⟨11,by decide⟩).lower ∧ (cell12686 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12686 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12686 ⟨12,by decide⟩).lower ∧ (cell12686 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12686 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12686 ⟨13,by decide⟩).lower ∧ (cell12686 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12686 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12686 ⟨14,by decide⟩).lower ∧ (cell12686 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12686 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12686 ⟨15,by decide⟩).lower ∧ (cell12686 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12686 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12686 ⟨16,by decide⟩).lower ∧ (cell12686 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12686 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12686 ⟨17,by decide⟩).lower ∧ (cell12686 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12686 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12686 ⟨18,by decide⟩).lower ∧ (cell12686 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12686 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12686 ⟨19,by decide⟩).lower ∧ (cell12686 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12686 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12686 ⟨20,by decide⟩).lower ∧ (cell12686 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12686 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12686 ⟨21,by decide⟩).lower ∧ (cell12686 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12686 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12686 ⟨22,by decide⟩).lower ∧ (cell12686 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12686 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12686 ⟨23,by decide⟩).lower ∧ (cell12686 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12686 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12686 ⟨24,by decide⟩).lower ∧ (cell12686 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12686 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12686 ⟨25,by decide⟩).lower ∧ (cell12686 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12686 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12686 ⟨26,by decide⟩).lower ∧ (cell12686 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12686 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12686 ⟨27,by decide⟩).lower ∧ (cell12686 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12686 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12686 ⟨28,by decide⟩).lower ∧ (cell12686 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12686 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12686 ⟨29,by decide⟩).lower ∧ (cell12686 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12686 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12686 ⟨30,by decide⟩).lower ∧ (cell12686 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12686 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12686 ⟨31,by decide⟩).lower ∧ (cell12686 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12686 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12686 ⟨32,by decide⟩).lower ∧ (cell12686 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12686 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12686 ⟨33,by decide⟩).lower ∧ (cell12686 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12686 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12686 ⟨34,by decide⟩).lower ∧ (cell12686 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12686 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12686 ⟨35,by decide⟩).lower ∧ (cell12686 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12686 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12686 ⟨36,by decide⟩).lower ∧ (cell12686 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12686 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12686 ⟨37,by decide⟩).lower ∧ (cell12686 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12686 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12686 ⟨38,by decide⟩).lower ∧ (cell12686 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12686 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12686 ⟨39,by decide⟩).lower ∧ (cell12686 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12686 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12686 ⟨40,by decide⟩).lower ∧ (cell12686 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12686 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12686 ⟨41,by decide⟩).lower ∧ (cell12686 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12686 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12686 ⟨42,by decide⟩).lower ∧ (cell12686 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12686 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12686 ⟨43,by decide⟩).lower ∧ (cell12686 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12686 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12686 ⟨44,by decide⟩).lower ∧ (cell12686 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12686 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12686 ⟨45,by decide⟩).lower ∧ (cell12686 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12686 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12686 ⟨46,by decide⟩).lower ∧ (cell12686 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12686 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12686 ⟨47,by decide⟩).lower ∧ (cell12686 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12686 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12686 ⟨48,by decide⟩).lower ∧ (cell12686 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12686 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12686 ⟨49,by decide⟩).lower ∧ (cell12686 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12686 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12686 ⟨50,by decide⟩).lower ∧ (cell12686 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12686 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12686 ⟨51,by decide⟩).lower ∧ (cell12686 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12686 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12686 ⟨52,by decide⟩).lower ∧ (cell12686 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12686 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12686 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12686 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12686,cell12686,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12686 i).lower ∧
    (cell12686 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12686 i).upper ≤ (0.532 : ℝ) ∧
    (cell12686 i).centre ≤ (0.1 : ℝ) ∧ (cell12686 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12686 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12686 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12686

/-! The local source numeric instances at 12686 have no network premises. -/
namespace BstLean.Part269.N12686
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12686)
open BstLean.Part268 (cell12686)

noncomputable def sourceNumerics12686 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12686 (cell12686 i)
      scalarRow12686.M scalarRow12686.H scalarRow12686.xi := by
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
    energy_allowance := scalarRow12686.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12686]
    centre_nonneg := (scalarRow12686.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12686])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12686
/-! Actual 12687 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12687 ≤ (1.035827724050 : ℝ) := by
  have hr : (112.636583755012 : ℝ) ≤ √(12687 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.636583755012 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12687 12687 (11 / 1000) ≤
    (0.008486470390 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12687) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.636583755012 : ℝ) ≤ √(12687 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12687)
  have hdiv : K / √(12687 : ℝ) ≤ K / 112.636583755012 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.636583755012 ≤ (0.008486470390 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12687.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12687 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12687 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12687 := gPlus_lower 12687
end BstLean.Part269.N12687

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12687
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035827724049 : ℝ) ≤ wn 12687 := by
  have hn : √(12687 : ℝ) ≤ 112.636583755013 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12687 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.636583755013 ≤ 2 / √(12687 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252143468 : ℝ) ≤ rhoBar 12687 BstLean.Part154.csC ∧
    rhoBar 12687 BstLean.Part154.csC ≤ 0.000252143858 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035827724049 : ℝ) / (1.295212 * 12687) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035827724050 : ℝ) / (1.29521 * 12687) := by gcongr
      _ ≤ (0.000252143858 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12687 BstLean.Part154.csC) ≤ 0.001008639009 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12687 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) ≤ 0.000192589189 ∧
    cc1 (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) ≤ 0.000122545778 ∧
    cc2 (rhoBar 12687 BstLean.Part154.csC) ≤ 0.000071138761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12687 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12687 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12687 BstLean.Part154.csC * nuR (rhoBar 12687 BstLean.Part154.csC)) ≤ 0.000504303610 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252143858 : ℝ) * 0.001008639009 := by gcongr
      _ ≤ (0.000504303610 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12687 BstLean.Part154.csC) * nuR (rhoBar 12687 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001008639009 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12687 BstLean.Part154.csC) * rhoBar 12687 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252143858 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252143858 / 2 + 0.399 * 0.001008639009 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192589189 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504303610 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122545778 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252143858 / 1.414213562 := by gcongr
      _ ≤ (0.000071138761 : ℝ) := by norm_num

end BstLean.Part269.N12687

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12687
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) ≤ 1.60177E-7 := by
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12687 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12687 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12687 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192589189 : ℝ) ^ 2 + 0.000122545778 ^ 2 + 3 * 0.000071138761 ^ 2 +
        2 * 0.797885 * 0.000192589189 * 0.000122545778 + 2 * 0.000192589189 * 0.000071138761 +
        4 * 0.797885 * 0.000122545778 * 0.000071138761 := by gcongr
    _ ≤ (1.60177E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12687 BstLean.Part154.csC Θ ≤ 0.002632085276 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12687 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12687 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12687 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035827724050 * 1.60177E-7 / (0.000252143468 : ℝ) := by gcongr
    _ ≤ 0.002632085276 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12687 BstLean.Part154.csC Θ ≤ 0.002920484009 + 0.000665083432 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12687 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12687 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035827724050 : ℝ) * ((2 * Θ * 0.000252143858 +
        (6863 / 10000) * 0.000252143858 * 12687 * 0.001008639009) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002920484009 + 0.000665083432 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12687 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12687 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12687 0.011 Θ ∧ gammaRatio 12687 0.011 Θ ≤ 0.000086680539 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12687 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035827724050 : ℝ) * 0.525 / ((1 - 0.011) * 12687) := by gcongr
      _ ≤ (0.000086680539 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12687 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12687 0.011 Θ) :=
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
    badAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615501984 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12687 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12687 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12687 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12687 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12687 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12687 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12687 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12687 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12687 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12687 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035827724050 : ℝ) * 12687 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615501984 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003535985993 + 0.003297168708 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12687

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12687
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12687 BstLean.Part154.csC) (piBar (rhoBar 12687 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12687 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12687 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12687 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12687 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12687 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12687 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12687 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12687 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12687 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12687 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052511487138 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12687) ≤ 0.010602572817 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12687 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035827724050)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010602572817 + 2 * 0.737676 / 12687) := by gcongr
    _ ≤ (0.052511487138 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12687 12 ≤ 0.0015 := by
  exact BstLean.Part269.S13.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12687

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12687
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502979790 : ℝ) ≤ plow 12687 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12687) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773599565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381844770) : eMP 12687 0.011 xi bn ≤ 0.001189618598 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12687 : ℝ) * (1 - 0.011))) ≤ 0.000588202647 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001381844770 / (12687 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588202647 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588202647 : ℝ) + 3.141593 * 0.052773599565 / (12687 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001189618598 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773599565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381844770) : PiBarMP 12687 12 0.011 xi bn ≤ 0.161334471611 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12687 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037173172720 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.015369481156 : ℝ) ≤ √((12687 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.636583755012 : ℝ) ≤ √(12687 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12687) ≤ 0.123693455522 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037173172720 + 0.052773599565 * 1.772454 / (2 * (112.015369481156 : ℝ))) * (1 + 0.001189618598) +
        8 / (12687 * 112.636583755012) + 0.123693455522 := by gcongr
    _ ≤ (0.161334471611 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773599565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381844770) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282236539244) :
    parallelOracle 12687 0.011 xi bn cd ≤ 0.162325963127 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12687 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12687 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502979790 : ℝ) ≤ plow 12687 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.636583755012 : ℝ) ≤ √(12687 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282236539244 : ℝ) / (2 * 0.560502979790 * 112.636583755012)) * 0.161334471611 +
        0.282236539244 ^ 2 / (2 * 0.560502979790 * 112.636583755012) := by gcongr
    _ ≤ (0.162325963127 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052773599565) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001381844770)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282236539244) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12687 12687 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502979790 : ℝ) ≤ plow 12687 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.636583755012 : ℝ) ≤ √(12687 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12687 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12687 Θ 1.22 ≤ 0.011773266339 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.636583755012 := by gcongr <;> linarith
      _ ≤ (0.011773266339 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12687 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12687 12687 0.011 ≤ 0.008486470390 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12687 12687 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12687 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12687 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12687 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12687 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162325963127 + 0.011773266339 + (0.008486470390 : ℝ) *
        (1 + 2 * (0.282236539244 + 0.011773266339) / (0.560502979790 * 112.636583755012))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12687]

end BstLean.Part269.N12687

/-! The original eight local profiles supply actual 12687 moment certificates. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12687 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052773599565 ∧
    0 ≤ bN 12687 BstLean.Part154.csC (groupTheta g) ∧ bN 12687 BstLean.Part154.csC (groupTheta g) ≤ 0.001381844770 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12687 12687 0.011
      (momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12687 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12687 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12687 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229725052106 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12687 0.011
      (momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12687 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12687
/-! The actual computed-centre upper energy formula at 12687. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12687

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12687)
open BstLean.Part268 (cell12687)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085528260038
  | 2 => 0.086471709604
  | 3 => 0.087413401298
  | 4 => 0.088354776770
  | 5 => 0.089297578989
  | 6 => 0.090243896904
  | 7 => 0.091196214272
  | 8 => 0.092157462725
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12687 12687 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12687 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003538895953 + 0.003300387184 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S13.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S13.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12687

/-! Actual upper energy certificates on all 43 source endpoints at 12687. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12687)
open BstLean.Part268 (cell12687)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12687 (gMinus 12687) (1 - (cell12687 i).lower) ≤ 1 ∧
    energyUpper 12687 (gMinus 12687) (BstLean.Part211.gPlus 12687)
      (finiteEnergy 12687 12687 0.011) (1 - (cell12687 i).lower) ≤
      (cell12687 i).energy := by
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
      have E := BstLean.Part269.S13.uniformEnergy10 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨10,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy11 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨11,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy12 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨12,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy13 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨13,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy14 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨14,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy15 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨15,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy16 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨16,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy17 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨17,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy18 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨18,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy19 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨19,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy20 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨20,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy21 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨21,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy22 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨22,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy23 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨23,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy24 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨24,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy25 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨25,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy26 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨26,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy27 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨27,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy28 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨28,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy29 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨29,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy30 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨30,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy31 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨31,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy32 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨32,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy33 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨33,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy34 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨34,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy35 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨35,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy36 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨36,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy37 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨37,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy38 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨38,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy39 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨39,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy40 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨40,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy41 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨41,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy42 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨42,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy43 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨43,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy44 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨44,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy45 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨45,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy46 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨46,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy47 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨47,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy48 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨48,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy49 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨49,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy50 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨50,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy51 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨51,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S13.uniformEnergy52 (n := 12687) (by norm_num)
        (q := 1 - (cell12687 ⟨52,by decide⟩).lower)
        (by norm_num [cell12687]) (by norm_num [cell12687])
      exact ⟨E.1,E.2.trans (by norm_num [cell12687])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12687

/-! Source-cell containment and simple scalar guards at 12687. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12687)
open BstLean.Part268 (cell12687)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12687 ⟨10,by decide⟩).lower ∧ (cell12687 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12687 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12687 ⟨11,by decide⟩).lower ∧ (cell12687 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12687 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12687 ⟨12,by decide⟩).lower ∧ (cell12687 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12687 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12687 ⟨13,by decide⟩).lower ∧ (cell12687 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12687 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12687 ⟨14,by decide⟩).lower ∧ (cell12687 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12687 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12687 ⟨15,by decide⟩).lower ∧ (cell12687 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12687 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12687 ⟨16,by decide⟩).lower ∧ (cell12687 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12687 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12687 ⟨17,by decide⟩).lower ∧ (cell12687 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12687 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12687 ⟨18,by decide⟩).lower ∧ (cell12687 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12687 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12687 ⟨19,by decide⟩).lower ∧ (cell12687 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12687 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12687 ⟨20,by decide⟩).lower ∧ (cell12687 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12687 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12687 ⟨21,by decide⟩).lower ∧ (cell12687 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12687 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12687 ⟨22,by decide⟩).lower ∧ (cell12687 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12687 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12687 ⟨23,by decide⟩).lower ∧ (cell12687 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12687 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12687 ⟨24,by decide⟩).lower ∧ (cell12687 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12687 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12687 ⟨25,by decide⟩).lower ∧ (cell12687 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12687 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12687 ⟨26,by decide⟩).lower ∧ (cell12687 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12687 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12687 ⟨27,by decide⟩).lower ∧ (cell12687 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12687 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12687 ⟨28,by decide⟩).lower ∧ (cell12687 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12687 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12687 ⟨29,by decide⟩).lower ∧ (cell12687 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12687 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12687 ⟨30,by decide⟩).lower ∧ (cell12687 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12687 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12687 ⟨31,by decide⟩).lower ∧ (cell12687 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12687 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12687 ⟨32,by decide⟩).lower ∧ (cell12687 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12687 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12687 ⟨33,by decide⟩).lower ∧ (cell12687 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12687 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12687 ⟨34,by decide⟩).lower ∧ (cell12687 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12687 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12687 ⟨35,by decide⟩).lower ∧ (cell12687 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12687 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12687 ⟨36,by decide⟩).lower ∧ (cell12687 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12687 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12687 ⟨37,by decide⟩).lower ∧ (cell12687 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12687 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12687 ⟨38,by decide⟩).lower ∧ (cell12687 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12687 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12687 ⟨39,by decide⟩).lower ∧ (cell12687 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12687 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12687 ⟨40,by decide⟩).lower ∧ (cell12687 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12687 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12687 ⟨41,by decide⟩).lower ∧ (cell12687 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12687 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12687 ⟨42,by decide⟩).lower ∧ (cell12687 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12687 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12687 ⟨43,by decide⟩).lower ∧ (cell12687 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12687 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12687 ⟨44,by decide⟩).lower ∧ (cell12687 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12687 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12687 ⟨45,by decide⟩).lower ∧ (cell12687 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12687 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12687 ⟨46,by decide⟩).lower ∧ (cell12687 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12687 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12687 ⟨47,by decide⟩).lower ∧ (cell12687 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12687 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12687 ⟨48,by decide⟩).lower ∧ (cell12687 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12687 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12687 ⟨49,by decide⟩).lower ∧ (cell12687 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12687 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12687 ⟨50,by decide⟩).lower ∧ (cell12687 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12687 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12687 ⟨51,by decide⟩).lower ∧ (cell12687 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12687 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12687 ⟨52,by decide⟩).lower ∧ (cell12687 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12687 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12687 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12687 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12687,cell12687,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12687 i).lower ∧
    (cell12687 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12687 i).upper ≤ (0.532 : ℝ) ∧
    (cell12687 i).centre ≤ (0.1 : ℝ) ∧ (cell12687 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12687 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12687 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12687

/-! The local source numeric instances at 12687 have no network premises. -/
namespace BstLean.Part269.N12687
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12687)
open BstLean.Part268 (cell12687)

noncomputable def sourceNumerics12687 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12687 (cell12687 i)
      scalarRow12687.M scalarRow12687.H scalarRow12687.xi := by
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
    energy_allowance := scalarRow12687.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12687]
    centre_nonneg := (scalarRow12687.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D13.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12687])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12687