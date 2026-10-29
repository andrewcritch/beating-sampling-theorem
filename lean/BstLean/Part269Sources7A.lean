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
import BstLean.Part269Direction7
import BstLean.Part269Shared7
import BstLean.Part269Finite
import BstLean.Part269Rows7
import BstLean.Part269Source
/-! Actual 12525 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12525 ≤ (1.036060725407 : ℝ) := by
  have hr : (111.915146427996 : ℝ) ≤ √(12525 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.915146427996 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12525 12525 (11 / 1000) ≤
    (0.008541177052 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12525) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.915146427996 : ℝ) ≤ √(12525 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12525)
  have hdiv : K / √(12525 : ℝ) ≤ K / 111.915146427996 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.915146427996 ≤ (0.008541177052 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12525.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12525 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12525 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12525 := gPlus_lower 12525
end BstLean.Part269.N12525

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12525
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036060725406 : ℝ) ≤ wn 12525 := by
  have hn : √(12525 : ℝ) ≤ 111.915146427997 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12525 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.915146427997 ≤ 2 / √(12525 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255462176 : ℝ) ≤ rhoBar 12525 BstLean.Part154.csC ∧
    rhoBar 12525 BstLean.Part154.csC ≤ 0.000255462572 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036060725406 : ℝ) / (1.295212 * 12525) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036060725407 : ℝ) / (1.29521 * 12525) := by gcongr
      _ ≤ (0.000255462572 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12525 BstLean.Part154.csC) ≤ 0.001021915550 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12525 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) ≤ 0.000195124165 ∧
    cc1 (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) ≤ 0.000124158775 ∧
    cc2 (rhoBar 12525 BstLean.Part154.csC) ≤ 0.000072075088 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12525 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12525 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12525 BstLean.Part154.csC * nuR (rhoBar 12525 BstLean.Part154.csC)) ≤ 0.000510941460 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255462572 : ℝ) * 0.001021915550 := by gcongr
      _ ≤ (0.000510941460 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12525 BstLean.Part154.csC) * nuR (rhoBar 12525 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021915550 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12525 BstLean.Part154.csC) * rhoBar 12525 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255462572 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255462572 / 2 + 0.399 * 0.001021915550 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195124165 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510941460 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124158775 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255462572 / 1.414213562 := by gcongr
      _ ≤ (0.000072075088 : ℝ) := by norm_num

end BstLean.Part269.N12525

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12525
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) ≤ 1.64421E-7 := by
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12525 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12525 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12525 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195124165 : ℝ) ^ 2 + 0.000124158775 ^ 2 + 3 * 0.000072075088 ^ 2 +
        2 * 0.797885 * 0.000195124165 * 0.000124158775 + 2 * 0.000195124165 * 0.000072075088 +
        4 * 0.797885 * 0.000124158775 * 0.000072075088 := by gcongr
    _ ≤ (1.64421E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12525 BstLean.Part154.csC Θ ≤ 0.002667324662 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12525 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12525 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12525 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036060725407 * 1.64421E-7 / (0.000255462176 : ℝ) := by gcongr
    _ ≤ 0.002667324662 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12525 BstLean.Part154.csC Θ ≤ 0.002960257168 + 0.000673988826 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12525 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12525 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036060725407 : ℝ) * ((2 * Θ * 0.000255462572 +
        (6863 / 10000) * 0.000255462572 * 12525 * 0.001021915550) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002960257168 + 0.000673988826 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12525 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12525 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12525 0.011 Θ ∧ gammaRatio 12525 0.011 Θ ≤ 0.000087821426 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12525 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036060725407 : ℝ) * 0.525 / ((1 - 0.011) * 12525) := by gcongr
      _ ≤ (0.000087821426 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12525 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12525 0.011 Θ) :=
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
    badAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12525 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12525 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12525 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12525 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12525 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12525 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12525 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12525 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12525 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12525 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036060725407 : ℝ) * 12525 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003703299838 + 0.003341313488 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12525

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12525
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12525 BstLean.Part154.csC) (piBar (rhoBar 12525 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12525 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12525 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12525 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12525 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12525 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12525 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12525 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12525 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12525 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12525 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052853687429 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12525) ≤ 0.010670920061 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12525 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036060725407)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010670920061 + 2 * 0.737676 / 12525) := by gcongr
    _ ≤ (0.052853687429 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12525 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12525

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12525
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495543696 : ℝ) ≤ plow 12525 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12525) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052964089420)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400345448) : eMP 12525 0.011 xi bn ≤ 0.001205320760 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12525 : ℝ) * (1 - 0.011))) ≤ 0.000595944121 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400345448 / (12525 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595944121 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595944121 : ℝ) + 3.141593 * 0.052964089420 / (12525 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205320760 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052964089420)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400345448) : PiBarMP 12525 12 0.011 xi bn ≤ 0.162385063956 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12525 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037421189827 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.297911031609 : ℝ) ≤ √((12525 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.915146427996 : ℝ) ≤ √(12525 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12525) ≤ 0.124490819228 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037421189827 + 0.052964089420 * 1.772454 / (2 * (111.297911031609 : ℝ))) * (1 + 0.001205320760) +
        8 / (12525 * 111.915146427996) + 0.124490819228 := by gcongr
    _ ≤ (0.162385063956 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052964089420)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400345448) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282992970082) :
    parallelOracle 12525 0.011 xi bn cd ≤ 0.163389710777 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12525 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12525 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495543696 : ℝ) ≤ plow 12525 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.915146427996 : ℝ) ≤ √(12525 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282992970082 : ℝ) / (2 * 0.560495543696 * 111.915146427996)) * 0.162385063956 +
        0.282992970082 ^ 2 / (2 * 0.560495543696 * 111.915146427996) := by gcongr
    _ ≤ (0.163389710777 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052964089420) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400345448)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282992970082) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12525 12525 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495543696 : ℝ) ≤ plow 12525 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.915146427996 : ℝ) ≤ √(12525 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12525 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12525 Θ 1.22 ≤ 0.011849160211 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.915146427996 := by gcongr <;> linarith
      _ ≤ (0.011849160211 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12525 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12525 12525 0.011 ≤ 0.008541177052 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12525 12525 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12525 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12525 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12525 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12525 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163389710777 + 0.011849160211 + (0.008541177052 : ℝ) *
        (1 + 2 * (0.282992970082 + 0.011849160211) / (0.560495543696 * 111.915146427996))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12525]

end BstLean.Part269.N12525

/-! The original eight local profiles supply actual 12525 moment certificates. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12525 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052964089420 ∧
    0 ≤ bN 12525 BstLean.Part154.csC (groupTheta g) ∧ bN 12525 BstLean.Part154.csC (groupTheta g) ≤ 0.001400345448 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12525 12525 0.011
      (momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12525 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12525 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12525 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230139282653 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12525 0.011
      (momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12525 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12525
/-! The actual computed-centre upper energy formula at 12525. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12525

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12525)
open BstLean.Part268 (cell12525)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086018244389
  | 2 => 0.086971105914
  | 3 => 0.087923647669
  | 4 => 0.088877637662
  | 5 => 0.089835201977
  | 6 => 0.090798876321
  | 7 => 0.091771662119
  | 8 => 0.092757087155
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12525 12525 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12525 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12525

/-! Actual upper energy certificates on all 43 source endpoints at 12525. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12525)
open BstLean.Part268 (cell12525)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12525 (gMinus 12525) (1 - (cell12525 i).lower) ≤ 1 ∧
    energyUpper 12525 (gMinus 12525) (BstLean.Part211.gPlus 12525)
      (finiteEnergy 12525 12525 0.011) (1 - (cell12525 i).lower) ≤
      (cell12525 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨10,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨11,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨12,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨13,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨14,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨15,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨16,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨17,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨18,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨19,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨20,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨21,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨22,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨23,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨24,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨25,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨26,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨27,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨28,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨29,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨30,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨31,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨32,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨33,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨34,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨35,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨36,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨37,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨38,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨39,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨40,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨41,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨42,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨43,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨44,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨45,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨46,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨47,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨48,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨49,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨50,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨51,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12525) (by norm_num)
        (q := 1 - (cell12525 ⟨52,by decide⟩).lower)
        (by norm_num [cell12525]) (by norm_num [cell12525])
      exact ⟨E.1,E.2.trans (by norm_num [cell12525])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12525

/-! Source-cell containment and simple scalar guards at 12525. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12525)
open BstLean.Part268 (cell12525)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12525 ⟨10,by decide⟩).lower ∧ (cell12525 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12525 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12525 ⟨11,by decide⟩).lower ∧ (cell12525 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12525 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12525 ⟨12,by decide⟩).lower ∧ (cell12525 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12525 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12525 ⟨13,by decide⟩).lower ∧ (cell12525 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12525 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12525 ⟨14,by decide⟩).lower ∧ (cell12525 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12525 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12525 ⟨15,by decide⟩).lower ∧ (cell12525 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12525 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12525 ⟨16,by decide⟩).lower ∧ (cell12525 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12525 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12525 ⟨17,by decide⟩).lower ∧ (cell12525 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12525 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12525 ⟨18,by decide⟩).lower ∧ (cell12525 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12525 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12525 ⟨19,by decide⟩).lower ∧ (cell12525 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12525 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12525 ⟨20,by decide⟩).lower ∧ (cell12525 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12525 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12525 ⟨21,by decide⟩).lower ∧ (cell12525 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12525 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12525 ⟨22,by decide⟩).lower ∧ (cell12525 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12525 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12525 ⟨23,by decide⟩).lower ∧ (cell12525 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12525 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12525 ⟨24,by decide⟩).lower ∧ (cell12525 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12525 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12525 ⟨25,by decide⟩).lower ∧ (cell12525 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12525 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12525 ⟨26,by decide⟩).lower ∧ (cell12525 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12525 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12525 ⟨27,by decide⟩).lower ∧ (cell12525 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12525 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12525 ⟨28,by decide⟩).lower ∧ (cell12525 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12525 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12525 ⟨29,by decide⟩).lower ∧ (cell12525 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12525 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12525 ⟨30,by decide⟩).lower ∧ (cell12525 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12525 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12525 ⟨31,by decide⟩).lower ∧ (cell12525 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12525 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12525 ⟨32,by decide⟩).lower ∧ (cell12525 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12525 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12525 ⟨33,by decide⟩).lower ∧ (cell12525 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12525 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12525 ⟨34,by decide⟩).lower ∧ (cell12525 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12525 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12525 ⟨35,by decide⟩).lower ∧ (cell12525 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12525 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12525 ⟨36,by decide⟩).lower ∧ (cell12525 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12525 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12525 ⟨37,by decide⟩).lower ∧ (cell12525 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12525 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12525 ⟨38,by decide⟩).lower ∧ (cell12525 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12525 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12525 ⟨39,by decide⟩).lower ∧ (cell12525 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12525 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12525 ⟨40,by decide⟩).lower ∧ (cell12525 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12525 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12525 ⟨41,by decide⟩).lower ∧ (cell12525 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12525 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12525 ⟨42,by decide⟩).lower ∧ (cell12525 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12525 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12525 ⟨43,by decide⟩).lower ∧ (cell12525 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12525 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12525 ⟨44,by decide⟩).lower ∧ (cell12525 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12525 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12525 ⟨45,by decide⟩).lower ∧ (cell12525 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12525 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12525 ⟨46,by decide⟩).lower ∧ (cell12525 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12525 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12525 ⟨47,by decide⟩).lower ∧ (cell12525 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12525 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12525 ⟨48,by decide⟩).lower ∧ (cell12525 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12525 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12525 ⟨49,by decide⟩).lower ∧ (cell12525 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12525 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12525 ⟨50,by decide⟩).lower ∧ (cell12525 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12525 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12525 ⟨51,by decide⟩).lower ∧ (cell12525 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12525 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12525 ⟨52,by decide⟩).lower ∧ (cell12525 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12525 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12525 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12525 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12525,cell12525,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12525 i).lower ∧
    (cell12525 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12525 i).upper ≤ (0.532 : ℝ) ∧
    (cell12525 i).centre ≤ (0.1 : ℝ) ∧ (cell12525 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12525 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12525 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12525

/-! The local source numeric instances at 12525 have no network premises. -/
namespace BstLean.Part269.N12525
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12525)
open BstLean.Part268 (cell12525)

noncomputable def sourceNumerics12525 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12525 (cell12525 i)
      scalarRow12525.M scalarRow12525.H scalarRow12525.xi := by
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
    energy_allowance := scalarRow12525.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12525]
    centre_nonneg := (scalarRow12525.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12525])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12525
/-! Actual 12526 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12526 ≤ (1.036059273195 : ℝ) := by
  have hr : (111.919614009341 : ℝ) ≤ √(12526 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.919614009341 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12526 12526 (11 / 1000) ≤
    (0.008540836105 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12526) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.919614009341 : ℝ) ≤ √(12526 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12526)
  have hdiv : K / √(12526 : ℝ) ≤ K / 111.919614009341 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.919614009341 ≤ (0.008540836105 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12526.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12526 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12526 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12526 := gPlus_lower 12526
end BstLean.Part269.N12526

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12526
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036059273194 : ℝ) ≤ wn 12526 := by
  have hn : √(12526 : ℝ) ≤ 111.919614009342 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12526 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.919614009342 ≤ 2 / √(12526 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255441424 : ℝ) ≤ rhoBar 12526 BstLean.Part154.csC ∧
    rhoBar 12526 BstLean.Part154.csC ≤ 0.000255441819 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036059273194 : ℝ) / (1.295212 * 12526) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036059273195 : ℝ) / (1.29521 * 12526) := by gcongr
      _ ≤ (0.000255441819 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12526 BstLean.Part154.csC) ≤ 0.001021832527 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12526 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) ≤ 0.000195108313 ∧
    cc1 (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) ≤ 0.000124148689 ∧
    cc2 (rhoBar 12526 BstLean.Part154.csC) ≤ 0.000072069233 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12526 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12526 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12526 BstLean.Part154.csC * nuR (rhoBar 12526 BstLean.Part154.csC)) ≤ 0.000510899951 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255441819 : ℝ) * 0.001021832527 := by gcongr
      _ ≤ (0.000510899951 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12526 BstLean.Part154.csC) * nuR (rhoBar 12526 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021832527 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12526 BstLean.Part154.csC) * rhoBar 12526 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255441819 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255441819 / 2 + 0.399 * 0.001021832527 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195108313 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510899951 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124148689 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255441819 / 1.414213562 := by gcongr
      _ ≤ (0.000072069233 : ℝ) := by norm_num

end BstLean.Part269.N12526

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12526
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) ≤ 1.64394E-7 := by
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12526 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12526 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12526 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195108313 : ℝ) ^ 2 + 0.000124148689 ^ 2 + 3 * 0.000072069233 ^ 2 +
        2 * 0.797885 * 0.000195108313 * 0.000124148689 + 2 * 0.000195108313 * 0.000072069233 +
        4 * 0.797885 * 0.000124148689 * 0.000072069233 := by gcongr
    _ ≤ (1.64394E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12526 BstLean.Part154.csC Θ ≤ 0.002667099573 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12526 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12526 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12526 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036059273195 * 1.64394E-7 / (0.000255441424 : ℝ) := by gcongr
    _ ≤ 0.002667099573 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12526 BstLean.Part154.csC Θ ≤ 0.002960008367 + 0.000673933128 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12526 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12526 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036059273195 : ℝ) * ((2 * Θ * 0.000255441819 +
        (6863 / 10000) * 0.000255441819 * 12526 * 0.001021832527) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002960008367 + 0.000673933128 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12526 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12526 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12526 0.011 Θ ∧ gammaRatio 12526 0.011 Θ ≤ 0.000087814292 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12526 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036059273195 : ℝ) * 0.525 / ((1 - 0.011) * 12526) := by gcongr
      _ ≤ (0.000087814292 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12526 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12526 0.011 Θ) :=
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
    badAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12526 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12526 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12526 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12526 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12526 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12526 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12526 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12526 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12526 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12526 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036059273195 : ℝ) * 12526 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003703051037 + 0.003341032701 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12526

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12526
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12526 BstLean.Part154.csC) (piBar (rhoBar 12526 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12526 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12526 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12526 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12526 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12526 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12526 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12526 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12526 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12526 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12526 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052851554591 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12526) ≤ 0.010670494101 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12526 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036059273195)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010670494101 + 2 * 0.737676 / 12526) := by gcongr
    _ ≤ (0.052851554591 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12526 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12526

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12526
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495590188 : ℝ) ≤ plow 12526 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12526) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963693206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400227276) : eMP 12526 0.011 xi bn ≤ 0.001205221719 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12526 : ℝ) * (1 - 0.011))) ≤ 0.000595895187 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400227276 / (12526 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595895187 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595895187 : ℝ) + 3.141593 * 0.052963693206 / (12526 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205221719 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963693206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400227276) : PiBarMP 12526 12 0.011 xi bn ≤ 0.162378489233 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12526 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037419610848 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.302353973310 : ℝ) ≤ √((12526 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.919614009341 : ℝ) ≤ √(12526 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12526) ≤ 0.124485849832 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037419610848 + 0.052963693206 * 1.772454 / (2 * (111.302353973310 : ℝ))) * (1 + 0.001205221719) +
        8 / (12526 * 111.919614009341) + 0.124485849832 := by gcongr
    _ ≤ (0.162378489233 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963693206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400227276) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282989976429) :
    parallelOracle 12526 0.011 xi bn cd ≤ 0.163383063658 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12526 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12526 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495590188 : ℝ) ≤ plow 12526 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.919614009341 : ℝ) ≤ √(12526 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282989976429 : ℝ) / (2 * 0.560495590188 * 111.919614009341)) * 0.162378489233 +
        0.282989976429 ^ 2 / (2 * 0.560495590188 * 111.919614009341) := by gcongr
    _ ≤ (0.163383063658 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963693206) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400227276)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282989976429) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12526 12526 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495590188 : ℝ) ≤ plow 12526 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.919614009341 : ℝ) ≤ √(12526 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12526 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12526 Θ 1.22 ≤ 0.011848687219 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.919614009341 := by gcongr <;> linarith
      _ ≤ (0.011848687219 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12526 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12526 12526 0.011 ≤ 0.008540836105 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12526 12526 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12526 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12526 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12526 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12526 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163383063658 + 0.011848687219 + (0.008540836105 : ℝ) *
        (1 + 2 * (0.282989976429 + 0.011848687219) / (0.560495590188 * 111.919614009341))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12526]

end BstLean.Part269.N12526

/-! The original eight local profiles supply actual 12526 moment certificates. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12526 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052963693206 ∧
    0 ≤ bN 12526 BstLean.Part154.csC (groupTheta g) ∧ bN 12526 BstLean.Part154.csC (groupTheta g) ≤ 0.001400227276 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12526 12526 0.011
      (momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12526 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12526 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12526 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230138421838 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12526 0.011
      (momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12526 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12526
/-! The actual computed-centre upper energy formula at 12526. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12526

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12526)
open BstLean.Part268 (cell12526)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086015120899
  | 2 => 0.086967920130
  | 3 => 0.087920389730
  | 4 => 0.088874295496
  | 5 => 0.089831760921
  | 6 => 0.090795318697
  | 7 => 0.091767966759
  | 8 => 0.092753228882
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12526 12526 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12526 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12526

/-! Actual upper energy certificates on all 43 source endpoints at 12526. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12526)
open BstLean.Part268 (cell12526)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12526 (gMinus 12526) (1 - (cell12526 i).lower) ≤ 1 ∧
    energyUpper 12526 (gMinus 12526) (BstLean.Part211.gPlus 12526)
      (finiteEnergy 12526 12526 0.011) (1 - (cell12526 i).lower) ≤
      (cell12526 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨10,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨11,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨12,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨13,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨14,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨15,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨16,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨17,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨18,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨19,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨20,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨21,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨22,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨23,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨24,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨25,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨26,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨27,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨28,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨29,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨30,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨31,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨32,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨33,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨34,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨35,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨36,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨37,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨38,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨39,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨40,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨41,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨42,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨43,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨44,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨45,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨46,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨47,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨48,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨49,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨50,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨51,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12526) (by norm_num)
        (q := 1 - (cell12526 ⟨52,by decide⟩).lower)
        (by norm_num [cell12526]) (by norm_num [cell12526])
      exact ⟨E.1,E.2.trans (by norm_num [cell12526])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12526

/-! Source-cell containment and simple scalar guards at 12526. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12526)
open BstLean.Part268 (cell12526)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12526 ⟨10,by decide⟩).lower ∧ (cell12526 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12526 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12526 ⟨11,by decide⟩).lower ∧ (cell12526 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12526 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12526 ⟨12,by decide⟩).lower ∧ (cell12526 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12526 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12526 ⟨13,by decide⟩).lower ∧ (cell12526 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12526 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12526 ⟨14,by decide⟩).lower ∧ (cell12526 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12526 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12526 ⟨15,by decide⟩).lower ∧ (cell12526 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12526 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12526 ⟨16,by decide⟩).lower ∧ (cell12526 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12526 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12526 ⟨17,by decide⟩).lower ∧ (cell12526 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12526 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12526 ⟨18,by decide⟩).lower ∧ (cell12526 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12526 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12526 ⟨19,by decide⟩).lower ∧ (cell12526 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12526 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12526 ⟨20,by decide⟩).lower ∧ (cell12526 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12526 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12526 ⟨21,by decide⟩).lower ∧ (cell12526 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12526 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12526 ⟨22,by decide⟩).lower ∧ (cell12526 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12526 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12526 ⟨23,by decide⟩).lower ∧ (cell12526 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12526 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12526 ⟨24,by decide⟩).lower ∧ (cell12526 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12526 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12526 ⟨25,by decide⟩).lower ∧ (cell12526 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12526 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12526 ⟨26,by decide⟩).lower ∧ (cell12526 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12526 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12526 ⟨27,by decide⟩).lower ∧ (cell12526 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12526 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12526 ⟨28,by decide⟩).lower ∧ (cell12526 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12526 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12526 ⟨29,by decide⟩).lower ∧ (cell12526 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12526 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12526 ⟨30,by decide⟩).lower ∧ (cell12526 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12526 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12526 ⟨31,by decide⟩).lower ∧ (cell12526 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12526 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12526 ⟨32,by decide⟩).lower ∧ (cell12526 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12526 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12526 ⟨33,by decide⟩).lower ∧ (cell12526 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12526 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12526 ⟨34,by decide⟩).lower ∧ (cell12526 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12526 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12526 ⟨35,by decide⟩).lower ∧ (cell12526 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12526 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12526 ⟨36,by decide⟩).lower ∧ (cell12526 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12526 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12526 ⟨37,by decide⟩).lower ∧ (cell12526 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12526 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12526 ⟨38,by decide⟩).lower ∧ (cell12526 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12526 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12526 ⟨39,by decide⟩).lower ∧ (cell12526 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12526 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12526 ⟨40,by decide⟩).lower ∧ (cell12526 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12526 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12526 ⟨41,by decide⟩).lower ∧ (cell12526 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12526 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12526 ⟨42,by decide⟩).lower ∧ (cell12526 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12526 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12526 ⟨43,by decide⟩).lower ∧ (cell12526 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12526 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12526 ⟨44,by decide⟩).lower ∧ (cell12526 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12526 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12526 ⟨45,by decide⟩).lower ∧ (cell12526 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12526 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12526 ⟨46,by decide⟩).lower ∧ (cell12526 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12526 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12526 ⟨47,by decide⟩).lower ∧ (cell12526 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12526 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12526 ⟨48,by decide⟩).lower ∧ (cell12526 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12526 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12526 ⟨49,by decide⟩).lower ∧ (cell12526 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12526 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12526 ⟨50,by decide⟩).lower ∧ (cell12526 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12526 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12526 ⟨51,by decide⟩).lower ∧ (cell12526 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12526 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12526 ⟨52,by decide⟩).lower ∧ (cell12526 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12526 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12526 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12526 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12526,cell12526,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12526 i).lower ∧
    (cell12526 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12526 i).upper ≤ (0.532 : ℝ) ∧
    (cell12526 i).centre ≤ (0.1 : ℝ) ∧ (cell12526 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12526 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12526 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12526

/-! The local source numeric instances at 12526 have no network premises. -/
namespace BstLean.Part269.N12526
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12526)
open BstLean.Part268 (cell12526)

noncomputable def sourceNumerics12526 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12526 (cell12526 i)
      scalarRow12526.M scalarRow12526.H scalarRow12526.xi := by
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
    energy_allowance := scalarRow12526.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12526]
    centre_nonneg := (scalarRow12526.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12526])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12526
/-! Actual 12527 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12527 ≤ (1.036057821159 : ℝ) := by
  have hr : (111.924081412357 : ℝ) ≤ √(12527 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.924081412357 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12527 12527 (11 / 1000) ≤
    (0.008540495198 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12527) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.924081412357 : ℝ) ≤ √(12527 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12527)
  have hdiv : K / √(12527 : ℝ) ≤ K / 111.924081412357 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.924081412357 ≤ (0.008540495198 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12527.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12527 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12527 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12527 := gPlus_lower 12527
end BstLean.Part269.N12527

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12527
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036057821158 : ℝ) ≤ wn 12527 := by
  have hn : √(12527 : ℝ) ≤ 111.924081412358 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12527 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.924081412358 ≤ 2 / √(12527 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255420674 : ℝ) ≤ rhoBar 12527 BstLean.Part154.csC ∧
    rhoBar 12527 BstLean.Part154.csC ≤ 0.000255421070 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036057821158 : ℝ) / (1.295212 * 12527) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036057821159 : ℝ) / (1.29521 * 12527) := by gcongr
      _ ≤ (0.000255421070 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12527 BstLean.Part154.csC) ≤ 0.001021749520 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12527 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) ≤ 0.000195092464 ∧
    cc1 (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) ≤ 0.000124138604 ∧
    cc2 (rhoBar 12527 BstLean.Part154.csC) ≤ 0.000072063379 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12527 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12527 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12527 BstLean.Part154.csC * nuR (rhoBar 12527 BstLean.Part154.csC)) ≤ 0.000510858450 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255421070 : ℝ) * 0.001021749520 := by gcongr
      _ ≤ (0.000510858450 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12527 BstLean.Part154.csC) * nuR (rhoBar 12527 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021749520 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12527 BstLean.Part154.csC) * rhoBar 12527 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255421070 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255421070 / 2 + 0.399 * 0.001021749520 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195092464 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510858450 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124138604 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255421070 / 1.414213562 := by gcongr
      _ ≤ (0.000072063379 : ℝ) := by norm_num

end BstLean.Part269.N12527

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12527
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) ≤ 1.64368E-7 := by
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12527 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12527 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12527 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195092464 : ℝ) ^ 2 + 0.000124138604 ^ 2 + 3 * 0.000072063379 ^ 2 +
        2 * 0.797885 * 0.000195092464 * 0.000124138604 + 2 * 0.000195092464 * 0.000072063379 +
        4 * 0.797885 * 0.000124138604 * 0.000072063379 := by gcongr
    _ ≤ (1.64368E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12527 BstLean.Part154.csC Θ ≤ 0.002666890652 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12527 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12527 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12527 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036057821159 * 1.64368E-7 / (0.000255420674 : ℝ) := by gcongr
    _ ≤ 0.002666890652 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12527 BstLean.Part154.csC Θ ≤ 0.002959759622 + 0.000673877442 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12527 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12527 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036057821159 : ℝ) * ((2 * Θ * 0.000255421070 +
        (6863 / 10000) * 0.000255421070 * 12527 * 0.001021749520) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002959759622 + 0.000673877442 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12527 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12527 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12527 0.011 Θ ∧ gammaRatio 12527 0.011 Θ ≤ 0.000087807159 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12527 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036057821159 : ℝ) * 0.525 / ((1 - 0.011) * 12527) := by gcongr
      _ ≤ (0.000087807159 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12527 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12527 0.011 Θ) :=
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
    badAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12527 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12527 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12527 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12527 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12527 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12527 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12527 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12527 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12527 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12527 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036057821159 : ℝ) * 12527 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003702802292 + 0.003340768094 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12527

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12527
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12527 BstLean.Part154.csC) (piBar (rhoBar 12527 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12527 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12527 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12527 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12527 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12527 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12527 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12527 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12527 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12527 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12527 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052849422014 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12527) ≤ 0.010670068193 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12527 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036057821159)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010670068193 + 2 * 0.737676 / 12527) := by gcongr
    _ ≤ (0.052849422014 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12527 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12527

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12527
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495636672 : ℝ) ≤ plow 12527 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12527) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963305542)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400117593) : eMP 12527 0.011 xi bn ≤ 0.001205126302 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12527 : ℝ) * (1 - 0.011))) ≤ 0.000595848064 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001400117593 / (12527 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595848064 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595848064 : ℝ) + 3.141593 * 0.052963305542 / (12527 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205126302 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963305542)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400117593) : PiBarMP 12527 12 0.011 xi bn ≤ 0.162372028819 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12527 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037418145238 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.306796737665 : ℝ) ≤ √((12527 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.924081412357 : ℝ) ≤ √(12527 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12527) ≤ 0.124480881031 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037418145238 + 0.052963305542 * 1.772454 / (2 * (111.306796737665 : ℝ))) * (1 + 0.001205126302) +
        8 / (12527 * 111.924081412357) + 0.124480881031 := by gcongr
    _ ≤ (0.162372028819 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963305542)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400117593) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282987001610) :
    parallelOracle 12527 0.011 xi bn cd ≤ 0.163376531222 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12527 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12527 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495636672 : ℝ) ≤ plow 12527 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.924081412357 : ℝ) ≤ √(12527 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282987001610 : ℝ) / (2 * 0.560495636672 * 111.924081412357)) * 0.162372028819 +
        0.282987001610 ^ 2 / (2 * 0.560495636672 * 111.924081412357) := by gcongr
    _ ≤ (0.163376531222 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052963305542) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001400117593)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282987001610) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12527 12527 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495636672 : ℝ) ≤ plow 12527 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.924081412357 : ℝ) ≤ √(12527 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12527 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12527 Θ 1.22 ≤ 0.011848214283 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.924081412357 := by gcongr <;> linarith
      _ ≤ (0.011848214283 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12527 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12527 12527 0.011 ≤ 0.008540495198 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12527 12527 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12527 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12527 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12527 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12527 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163376531222 + 0.011848214283 + (0.008540495198 : ℝ) *
        (1 + 2 * (0.282987001610 + 0.011848214283) / (0.560495636672 * 111.924081412357))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12527]

end BstLean.Part269.N12527

/-! The original eight local profiles supply actual 12527 moment certificates. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12527 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052963305542 ∧
    0 ≤ bN 12527 BstLean.Part154.csC (groupTheta g) ∧ bN 12527 BstLean.Part154.csC (groupTheta g) ≤ 0.001400117593 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12527 12527 0.011
      (momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12527 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12527 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12527 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230137579596 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12527 0.011
      (momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12527 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12527
/-! The actual computed-centre upper energy formula at 12527. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12527

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12527)
open BstLean.Part268 (cell12527)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086011998708
  | 2 => 0.086964735699
  | 3 => 0.087917133213
  | 4 => 0.088870954837
  | 5 => 0.089828321476
  | 6 => 0.090791762809
  | 7 => 0.091764273287
  | 8 => 0.092749372676
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12527 12527 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12527 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12527

/-! Actual upper energy certificates on all 43 source endpoints at 12527. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12527)
open BstLean.Part268 (cell12527)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12527 (gMinus 12527) (1 - (cell12527 i).lower) ≤ 1 ∧
    energyUpper 12527 (gMinus 12527) (BstLean.Part211.gPlus 12527)
      (finiteEnergy 12527 12527 0.011) (1 - (cell12527 i).lower) ≤
      (cell12527 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨10,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨11,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨12,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨13,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨14,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨15,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨16,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨17,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨18,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨19,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨20,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨21,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨22,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨23,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨24,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨25,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨26,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨27,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨28,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨29,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨30,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨31,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨32,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨33,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨34,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨35,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨36,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨37,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨38,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨39,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨40,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨41,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨42,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨43,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨44,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨45,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨46,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨47,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨48,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨49,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨50,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨51,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12527) (by norm_num)
        (q := 1 - (cell12527 ⟨52,by decide⟩).lower)
        (by norm_num [cell12527]) (by norm_num [cell12527])
      exact ⟨E.1,E.2.trans (by norm_num [cell12527])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12527

/-! Source-cell containment and simple scalar guards at 12527. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12527)
open BstLean.Part268 (cell12527)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12527 ⟨10,by decide⟩).lower ∧ (cell12527 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12527 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12527 ⟨11,by decide⟩).lower ∧ (cell12527 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12527 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12527 ⟨12,by decide⟩).lower ∧ (cell12527 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12527 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12527 ⟨13,by decide⟩).lower ∧ (cell12527 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12527 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12527 ⟨14,by decide⟩).lower ∧ (cell12527 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12527 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12527 ⟨15,by decide⟩).lower ∧ (cell12527 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12527 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12527 ⟨16,by decide⟩).lower ∧ (cell12527 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12527 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12527 ⟨17,by decide⟩).lower ∧ (cell12527 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12527 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12527 ⟨18,by decide⟩).lower ∧ (cell12527 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12527 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12527 ⟨19,by decide⟩).lower ∧ (cell12527 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12527 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12527 ⟨20,by decide⟩).lower ∧ (cell12527 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12527 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12527 ⟨21,by decide⟩).lower ∧ (cell12527 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12527 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12527 ⟨22,by decide⟩).lower ∧ (cell12527 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12527 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12527 ⟨23,by decide⟩).lower ∧ (cell12527 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12527 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12527 ⟨24,by decide⟩).lower ∧ (cell12527 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12527 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12527 ⟨25,by decide⟩).lower ∧ (cell12527 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12527 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12527 ⟨26,by decide⟩).lower ∧ (cell12527 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12527 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12527 ⟨27,by decide⟩).lower ∧ (cell12527 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12527 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12527 ⟨28,by decide⟩).lower ∧ (cell12527 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12527 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12527 ⟨29,by decide⟩).lower ∧ (cell12527 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12527 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12527 ⟨30,by decide⟩).lower ∧ (cell12527 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12527 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12527 ⟨31,by decide⟩).lower ∧ (cell12527 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12527 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12527 ⟨32,by decide⟩).lower ∧ (cell12527 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12527 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12527 ⟨33,by decide⟩).lower ∧ (cell12527 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12527 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12527 ⟨34,by decide⟩).lower ∧ (cell12527 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12527 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12527 ⟨35,by decide⟩).lower ∧ (cell12527 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12527 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12527 ⟨36,by decide⟩).lower ∧ (cell12527 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12527 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12527 ⟨37,by decide⟩).lower ∧ (cell12527 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12527 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12527 ⟨38,by decide⟩).lower ∧ (cell12527 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12527 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12527 ⟨39,by decide⟩).lower ∧ (cell12527 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12527 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12527 ⟨40,by decide⟩).lower ∧ (cell12527 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12527 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12527 ⟨41,by decide⟩).lower ∧ (cell12527 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12527 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12527 ⟨42,by decide⟩).lower ∧ (cell12527 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12527 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12527 ⟨43,by decide⟩).lower ∧ (cell12527 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12527 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12527 ⟨44,by decide⟩).lower ∧ (cell12527 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12527 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12527 ⟨45,by decide⟩).lower ∧ (cell12527 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12527 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12527 ⟨46,by decide⟩).lower ∧ (cell12527 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12527 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12527 ⟨47,by decide⟩).lower ∧ (cell12527 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12527 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12527 ⟨48,by decide⟩).lower ∧ (cell12527 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12527 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12527 ⟨49,by decide⟩).lower ∧ (cell12527 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12527 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12527 ⟨50,by decide⟩).lower ∧ (cell12527 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12527 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12527 ⟨51,by decide⟩).lower ∧ (cell12527 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12527 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12527 ⟨52,by decide⟩).lower ∧ (cell12527 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12527 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12527 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12527 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12527,cell12527,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12527 i).lower ∧
    (cell12527 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12527 i).upper ≤ (0.532 : ℝ) ∧
    (cell12527 i).centre ≤ (0.1 : ℝ) ∧ (cell12527 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12527 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12527 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12527

/-! The local source numeric instances at 12527 have no network premises. -/
namespace BstLean.Part269.N12527
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12527)
open BstLean.Part268 (cell12527)

noncomputable def sourceNumerics12527 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12527 (cell12527 i)
      scalarRow12527.M scalarRow12527.H scalarRow12527.xi := by
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
    energy_allowance := scalarRow12527.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12527]
    centre_nonneg := (scalarRow12527.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12527])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12527
/-! Actual 12528 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12528 ≤ (1.036056369297 : ℝ) := by
  have hr : (111.928548637065 : ℝ) ≤ √(12528 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.928548637065 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12528 12528 (11 / 1000) ≤
    (0.008540154333 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12528) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.928548637065 : ℝ) ≤ √(12528 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12528)
  have hdiv : K / √(12528 : ℝ) ≤ K / 111.928548637065 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.928548637065 ≤ (0.008540154333 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12528.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12528 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12528 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12528 := gPlus_lower 12528
end BstLean.Part269.N12528

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12528
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036056369296 : ℝ) ≤ wn 12528 := by
  have hn : √(12528 : ℝ) ≤ 111.928548637066 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12528 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.928548637066 ≤ 2 / √(12528 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255399928 : ℝ) ≤ rhoBar 12528 BstLean.Part154.csC ∧
    rhoBar 12528 BstLean.Part154.csC ≤ 0.000255400324 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036056369296 : ℝ) / (1.295212 * 12528) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036056369297 : ℝ) / (1.29521 * 12528) := by gcongr
      _ ≤ (0.000255400324 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12528 BstLean.Part154.csC) ≤ 0.001021666526 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12528 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) ≤ 0.000195076617 ∧
    cc1 (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) ≤ 0.000124128521 ∧
    cc2 (rhoBar 12528 BstLean.Part154.csC) ≤ 0.000072057526 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12528 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12528 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12528 BstLean.Part154.csC * nuR (rhoBar 12528 BstLean.Part154.csC)) ≤ 0.000510816956 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255400324 : ℝ) * 0.001021666526 := by gcongr
      _ ≤ (0.000510816956 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12528 BstLean.Part154.csC) * nuR (rhoBar 12528 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021666526 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12528 BstLean.Part154.csC) * rhoBar 12528 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255400324 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255400324 / 2 + 0.399 * 0.001021666526 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195076617 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510816956 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124128521 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255400324 / 1.414213562 := by gcongr
      _ ≤ (0.000072057526 : ℝ) := by norm_num

end BstLean.Part269.N12528

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12528
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) ≤ 1.64341E-7 := by
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12528 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12528 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12528 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195076617 : ℝ) ^ 2 + 0.000124128521 ^ 2 + 3 * 0.000072057526 ^ 2 +
        2 * 0.797885 * 0.000195076617 * 0.000124128521 + 2 * 0.000195076617 * 0.000072057526 +
        4 * 0.797885 * 0.000124128521 * 0.000072057526 := by gcongr
    _ ≤ (1.64341E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12528 BstLean.Part154.csC Θ ≤ 0.002666665432 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12528 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12528 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12528 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036056369297 * 1.64341E-7 / (0.000255399928 : ℝ) := by gcongr
    _ ≤ 0.002666665432 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12528 BstLean.Part154.csC Θ ≤ 0.002959510914 + 0.000673821763 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12528 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12528 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036056369297 : ℝ) * ((2 * Θ * 0.000255400324 +
        (6863 / 10000) * 0.000255400324 * 12528 * 0.001021666526) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002959510914 + 0.000673821763 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12528 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12528 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12528 0.011 Θ ∧ gammaRatio 12528 0.011 Θ ≤ 0.000087800027 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12528 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036056369297 : ℝ) * 0.525 / ((1 - 0.011) * 12528) := by gcongr
      _ ≤ (0.000087800027 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12528 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12528 0.011 Θ) :=
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
    badAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12528 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12528 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12528 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12528 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12528 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12528 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12528 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12528 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12528 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12528 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036056369297 : ℝ) * 12528 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003702553584 + 0.003340487195 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12528

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12528
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12528 BstLean.Part154.csC) (piBar (rhoBar 12528 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12528 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12528 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12528 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12528 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12528 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12528 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12528 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12528 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12528 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12528 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052847289694 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12528) ≤ 0.010669642336 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12528 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036056369297)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010669642336 + 2 * 0.737676 / 12528) := by gcongr
    _ ≤ (0.052847289694 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12528 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12528

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12528
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495683149 : ℝ) ≤ plow 12528 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12528) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962909362)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399999352) : eMP 12528 0.011 xi bn ≤ 0.001205027248 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12528 : ℝ) * (1 - 0.011))) ≤ 0.000595799123 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399999352 / (12528 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595799123 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595799123 : ℝ) + 3.141593 * 0.052962909362 / (12528 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001205027248 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962909362)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399999352) : PiBarMP 12528 12 0.011 xi bn ≤ 0.162365454240 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12528 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037416565209 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.311239324697 : ℝ) ≤ √((12528 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.928548637065 : ℝ) ≤ √(12528 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12528) ≤ 0.124475912825 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037416565209 + 0.052962909362 * 1.772454 / (2 * (111.311239324697 : ℝ))) * (1 + 0.001205027248) +
        8 / (12528 * 111.928548637065) + 0.124475912825 := by gcongr
    _ ≤ (0.162365454240 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962909362)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399999352) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282984008542) :
    parallelOracle 12528 0.011 xi bn cd ≤ 0.163369884267 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12528 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12528 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495683149 : ℝ) ≤ plow 12528 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.928548637065 : ℝ) ≤ √(12528 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282984008542 : ℝ) / (2 * 0.560495683149 * 111.928548637065)) * 0.162365454240 +
        0.282984008542 ^ 2 / (2 * 0.560495683149 * 111.928548637065) := by gcongr
    _ ≤ (0.163369884267 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962909362) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399999352)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282984008542) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12528 12528 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495683149 : ℝ) ≤ plow 12528 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.928548637065 : ℝ) ≤ √(12528 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12528 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12528 Θ 1.22 ≤ 0.011847741405 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.928548637065 := by gcongr <;> linarith
      _ ≤ (0.011847741405 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12528 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12528 12528 0.011 ≤ 0.008540154333 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12528 12528 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12528 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12528 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12528 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12528 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163369884267 + 0.011847741405 + (0.008540154333 : ℝ) *
        (1 + 2 * (0.282984008542 + 0.011847741405) / (0.560495683149 * 111.928548637065))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12528]

end BstLean.Part269.N12528

/-! The original eight local profiles supply actual 12528 moment certificates. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12528 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052962909362 ∧
    0 ≤ bN 12528 BstLean.Part154.csC (groupTheta g) ∧ bN 12528 BstLean.Part154.csC (groupTheta g) ≤ 0.001399999352 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12528 12528 0.011
      (momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12528 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12528 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12528 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230136718848 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12528 0.011
      (momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12528 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12528
/-! The actual computed-centre upper energy formula at 12528. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12528

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12528)
open BstLean.Part268 (cell12528)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086008877813
  | 2 => 0.086961552622
  | 3 => 0.087913878118
  | 4 => 0.088867615685
  | 5 => 0.089824883640
  | 6 => 0.090788208655
  | 7 => 0.091760581699
  | 8 => 0.092745518537
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12528 12528 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12528 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12528

/-! Actual upper energy certificates on all 43 source endpoints at 12528. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12528)
open BstLean.Part268 (cell12528)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12528 (gMinus 12528) (1 - (cell12528 i).lower) ≤ 1 ∧
    energyUpper 12528 (gMinus 12528) (BstLean.Part211.gPlus 12528)
      (finiteEnergy 12528 12528 0.011) (1 - (cell12528 i).lower) ≤
      (cell12528 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨10,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨11,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨12,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨13,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨14,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨15,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨16,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨17,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨18,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨19,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨20,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨21,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨22,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨23,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨24,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨25,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨26,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨27,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨28,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨29,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨30,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨31,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨32,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨33,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨34,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨35,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨36,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨37,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨38,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨39,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨40,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨41,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨42,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨43,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨44,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨45,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨46,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨47,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨48,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨49,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨50,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨51,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12528) (by norm_num)
        (q := 1 - (cell12528 ⟨52,by decide⟩).lower)
        (by norm_num [cell12528]) (by norm_num [cell12528])
      exact ⟨E.1,E.2.trans (by norm_num [cell12528])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12528

/-! Source-cell containment and simple scalar guards at 12528. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12528)
open BstLean.Part268 (cell12528)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12528 ⟨10,by decide⟩).lower ∧ (cell12528 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12528 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12528 ⟨11,by decide⟩).lower ∧ (cell12528 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12528 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12528 ⟨12,by decide⟩).lower ∧ (cell12528 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12528 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12528 ⟨13,by decide⟩).lower ∧ (cell12528 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12528 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12528 ⟨14,by decide⟩).lower ∧ (cell12528 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12528 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12528 ⟨15,by decide⟩).lower ∧ (cell12528 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12528 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12528 ⟨16,by decide⟩).lower ∧ (cell12528 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12528 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12528 ⟨17,by decide⟩).lower ∧ (cell12528 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12528 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12528 ⟨18,by decide⟩).lower ∧ (cell12528 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12528 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12528 ⟨19,by decide⟩).lower ∧ (cell12528 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12528 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12528 ⟨20,by decide⟩).lower ∧ (cell12528 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12528 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12528 ⟨21,by decide⟩).lower ∧ (cell12528 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12528 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12528 ⟨22,by decide⟩).lower ∧ (cell12528 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12528 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12528 ⟨23,by decide⟩).lower ∧ (cell12528 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12528 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12528 ⟨24,by decide⟩).lower ∧ (cell12528 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12528 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12528 ⟨25,by decide⟩).lower ∧ (cell12528 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12528 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12528 ⟨26,by decide⟩).lower ∧ (cell12528 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12528 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12528 ⟨27,by decide⟩).lower ∧ (cell12528 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12528 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12528 ⟨28,by decide⟩).lower ∧ (cell12528 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12528 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12528 ⟨29,by decide⟩).lower ∧ (cell12528 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12528 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12528 ⟨30,by decide⟩).lower ∧ (cell12528 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12528 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12528 ⟨31,by decide⟩).lower ∧ (cell12528 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12528 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12528 ⟨32,by decide⟩).lower ∧ (cell12528 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12528 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12528 ⟨33,by decide⟩).lower ∧ (cell12528 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12528 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12528 ⟨34,by decide⟩).lower ∧ (cell12528 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12528 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12528 ⟨35,by decide⟩).lower ∧ (cell12528 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12528 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12528 ⟨36,by decide⟩).lower ∧ (cell12528 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12528 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12528 ⟨37,by decide⟩).lower ∧ (cell12528 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12528 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12528 ⟨38,by decide⟩).lower ∧ (cell12528 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12528 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12528 ⟨39,by decide⟩).lower ∧ (cell12528 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12528 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12528 ⟨40,by decide⟩).lower ∧ (cell12528 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12528 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12528 ⟨41,by decide⟩).lower ∧ (cell12528 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12528 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12528 ⟨42,by decide⟩).lower ∧ (cell12528 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12528 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12528 ⟨43,by decide⟩).lower ∧ (cell12528 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12528 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12528 ⟨44,by decide⟩).lower ∧ (cell12528 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12528 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12528 ⟨45,by decide⟩).lower ∧ (cell12528 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12528 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12528 ⟨46,by decide⟩).lower ∧ (cell12528 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12528 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12528 ⟨47,by decide⟩).lower ∧ (cell12528 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12528 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12528 ⟨48,by decide⟩).lower ∧ (cell12528 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12528 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12528 ⟨49,by decide⟩).lower ∧ (cell12528 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12528 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12528 ⟨50,by decide⟩).lower ∧ (cell12528 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12528 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12528 ⟨51,by decide⟩).lower ∧ (cell12528 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12528 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12528 ⟨52,by decide⟩).lower ∧ (cell12528 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12528 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12528 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12528 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12528,cell12528,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12528 i).lower ∧
    (cell12528 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12528 i).upper ≤ (0.532 : ℝ) ∧
    (cell12528 i).centre ≤ (0.1 : ℝ) ∧ (cell12528 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12528 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12528 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12528

/-! The local source numeric instances at 12528 have no network premises. -/
namespace BstLean.Part269.N12528
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12528)
open BstLean.Part268 (cell12528)

noncomputable def sourceNumerics12528 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12528 (cell12528 i)
      scalarRow12528.M scalarRow12528.H scalarRow12528.xi := by
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
    energy_allowance := scalarRow12528.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12528]
    centre_nonneg := (scalarRow12528.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12528])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12528
/-! Actual 12529 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12529 ≤ (1.036054917610 : ℝ) := by
  have hr : (111.933015683488 : ℝ) ≤ √(12529 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.933015683488 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12529 12529 (11 / 1000) ≤
    (0.008539813508 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12529) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.933015683488 : ℝ) ≤ √(12529 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12529)
  have hdiv : K / √(12529 : ℝ) ≤ K / 111.933015683488 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.933015683488 ≤ (0.008539813508 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12529.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12529 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12529 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12529 := gPlus_lower 12529
end BstLean.Part269.N12529

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12529
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036054917609 : ℝ) ≤ wn 12529 := by
  have hn : √(12529 : ℝ) ≤ 111.933015683489 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12529 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.933015683489 ≤ 2 / √(12529 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255379186 : ℝ) ≤ rhoBar 12529 BstLean.Part154.csC ∧
    rhoBar 12529 BstLean.Part154.csC ≤ 0.000255379581 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036054917609 : ℝ) / (1.295212 * 12529) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036054917610 : ℝ) / (1.29521 * 12529) := by gcongr
      _ ≤ (0.000255379581 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12529 BstLean.Part154.csC) ≤ 0.001021583543 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12529 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) ≤ 0.000195060773 ∧
    cc1 (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) ≤ 0.000124118439 ∧
    cc2 (rhoBar 12529 BstLean.Part154.csC) ≤ 0.000072051673 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12529 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12529 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12529 BstLean.Part154.csC * nuR (rhoBar 12529 BstLean.Part154.csC)) ≤ 0.000510775467 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255379581 : ℝ) * 0.001021583543 := by gcongr
      _ ≤ (0.000510775467 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12529 BstLean.Part154.csC) * nuR (rhoBar 12529 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021583543 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12529 BstLean.Part154.csC) * rhoBar 12529 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255379581 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255379581 / 2 + 0.399 * 0.001021583543 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195060773 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510775467 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124118439 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255379581 / 1.414213562 := by gcongr
      _ ≤ (0.000072051673 : ℝ) := by norm_num

end BstLean.Part269.N12529

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12529
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) ≤ 1.64314E-7 := by
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12529 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12529 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12529 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195060773 : ℝ) ^ 2 + 0.000124118439 ^ 2 + 3 * 0.000072051673 ^ 2 +
        2 * 0.797885 * 0.000195060773 * 0.000124118439 + 2 * 0.000195060773 * 0.000072051673 +
        4 * 0.797885 * 0.000124118439 * 0.000072051673 := by gcongr
    _ ≤ (1.64314E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12529 BstLean.Part154.csC Θ ≤ 0.002666440134 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12529 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12529 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12529 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036054917610 * 1.64314E-7 / (0.000255379186 : ℝ) := by gcongr
    _ ≤ 0.002666440134 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12529 BstLean.Part154.csC Θ ≤ 0.002959262235 + 0.000673766093 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12529 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12529 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036054917610 : ℝ) * ((2 * Θ * 0.000255379581 +
        (6863 / 10000) * 0.000255379581 * 12529 * 0.001021583543) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002959262235 + 0.000673766093 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12529 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12529 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12529 0.011 Θ ∧ gammaRatio 12529 0.011 Θ ≤ 0.000087792896 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12529 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036054917610 : ℝ) * 0.525 / ((1 - 0.011) * 12529) := by gcongr
      _ ≤ (0.000087792896 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12529 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12529 0.011 Θ) :=
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
    badAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12529 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12529 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12529 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12529 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12529 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12529 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12529 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12529 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12529 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12529 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036054917610 : ℝ) * 12529 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003702304905 + 0.003340206227 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12529

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12529
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12529 BstLean.Part154.csC) (piBar (rhoBar 12529 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12529 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12529 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12529 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12529 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12529 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12529 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12529 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12529 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12529 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12529 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052845157627 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12529) ≤ 0.010669216529 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12529 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036054917610)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010669216529 + 2 * 0.737676 / 12529) := by gcongr
    _ ≤ (0.052845157627 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12529 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12529

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12529
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495729619 : ℝ) ≤ plow 12529 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12529) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962513175)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399881071) : eMP 12529 0.011 xi bn ≤ 0.001204928186 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12529 : ℝ) * (1 - 0.011))) ≤ 0.000595750178 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399881071 / (12529 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595750178 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595750178 : ℝ) + 3.141593 * 0.052962513175 / (12529 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204928186 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962513175)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399881071) : PiBarMP 12529 12 0.011 xi bn ≤ 0.162358879656 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12529 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037414984579 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.315681734425 : ℝ) ≤ √((12529 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.933015683488 : ℝ) ≤ √(12529 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12529) ≤ 0.124470945214 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037414984579 + 0.052962513175 * 1.772454 / (2 * (111.315681734425 : ℝ))) * (1 + 0.001204928186) +
        8 / (12529 * 111.933015683488) + 0.124470945214 := by gcongr
    _ ≤ (0.162358879656 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962513175)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399881071) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282981015709) :
    parallelOracle 12529 0.011 xi bn cd ≤ 0.163363237315 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12529 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12529 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495729619 : ℝ) ≤ plow 12529 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.933015683488 : ℝ) ≤ √(12529 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282981015709 : ℝ) / (2 * 0.560495729619 * 111.933015683488)) * 0.162358879656 +
        0.282981015709 ^ 2 / (2 * 0.560495729619 * 111.933015683488) := by gcongr
    _ ≤ (0.163363237315 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962513175) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399881071)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282981015709) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12529 12529 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495729619 : ℝ) ≤ plow 12529 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.933015683488 : ℝ) ≤ √(12529 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12529 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12529 Θ 1.22 ≤ 0.011847268583 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.933015683488 := by gcongr <;> linarith
      _ ≤ (0.011847268583 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12529 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12529 12529 0.011 ≤ 0.008539813508 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12529 12529 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12529 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12529 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12529 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12529 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163363237315 + 0.011847268583 + (0.008539813508 : ℝ) *
        (1 + 2 * (0.282981015709 + 0.011847268583) / (0.560495729619 * 111.933015683488))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12529]

end BstLean.Part269.N12529

/-! The original eight local profiles supply actual 12529 moment certificates. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12529 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052962513175 ∧
    0 ≤ bN 12529 BstLean.Part154.csC (groupTheta g) ∧ bN 12529 BstLean.Part154.csC (groupTheta g) ≤ 0.001399881071 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12529 12529 0.011
      (momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12529 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12529 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12529 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230135858082 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12529 0.011
      (momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12529 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12529
/-! The actual computed-centre upper energy formula at 12529. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12529

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12529)
open BstLean.Part268 (cell12529)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086005758213
  | 2 => 0.086958370895
  | 3 => 0.087910624443
  | 4 => 0.088864278036
  | 5 => 0.089821447412
  | 6 => 0.090784656233
  | 7 => 0.091756891993
  | 8 => 0.092741666461
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12529 12529 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12529 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12529

/-! Actual upper energy certificates on all 43 source endpoints at 12529. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12529)
open BstLean.Part268 (cell12529)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12529 (gMinus 12529) (1 - (cell12529 i).lower) ≤ 1 ∧
    energyUpper 12529 (gMinus 12529) (BstLean.Part211.gPlus 12529)
      (finiteEnergy 12529 12529 0.011) (1 - (cell12529 i).lower) ≤
      (cell12529 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨10,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨11,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨12,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨13,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨14,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨15,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨16,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨17,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨18,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨19,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨20,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨21,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨22,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨23,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨24,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨25,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨26,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨27,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨28,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨29,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨30,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨31,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨32,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨33,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨34,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨35,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨36,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨37,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨38,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨39,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨40,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨41,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨42,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨43,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨44,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨45,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨46,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨47,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨48,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨49,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨50,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨51,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12529) (by norm_num)
        (q := 1 - (cell12529 ⟨52,by decide⟩).lower)
        (by norm_num [cell12529]) (by norm_num [cell12529])
      exact ⟨E.1,E.2.trans (by norm_num [cell12529])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12529

/-! Source-cell containment and simple scalar guards at 12529. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12529)
open BstLean.Part268 (cell12529)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12529 ⟨10,by decide⟩).lower ∧ (cell12529 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12529 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12529 ⟨11,by decide⟩).lower ∧ (cell12529 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12529 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12529 ⟨12,by decide⟩).lower ∧ (cell12529 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12529 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12529 ⟨13,by decide⟩).lower ∧ (cell12529 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12529 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12529 ⟨14,by decide⟩).lower ∧ (cell12529 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12529 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12529 ⟨15,by decide⟩).lower ∧ (cell12529 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12529 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12529 ⟨16,by decide⟩).lower ∧ (cell12529 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12529 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12529 ⟨17,by decide⟩).lower ∧ (cell12529 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12529 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12529 ⟨18,by decide⟩).lower ∧ (cell12529 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12529 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12529 ⟨19,by decide⟩).lower ∧ (cell12529 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12529 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12529 ⟨20,by decide⟩).lower ∧ (cell12529 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12529 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12529 ⟨21,by decide⟩).lower ∧ (cell12529 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12529 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12529 ⟨22,by decide⟩).lower ∧ (cell12529 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12529 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12529 ⟨23,by decide⟩).lower ∧ (cell12529 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12529 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12529 ⟨24,by decide⟩).lower ∧ (cell12529 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12529 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12529 ⟨25,by decide⟩).lower ∧ (cell12529 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12529 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12529 ⟨26,by decide⟩).lower ∧ (cell12529 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12529 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12529 ⟨27,by decide⟩).lower ∧ (cell12529 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12529 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12529 ⟨28,by decide⟩).lower ∧ (cell12529 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12529 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12529 ⟨29,by decide⟩).lower ∧ (cell12529 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12529 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12529 ⟨30,by decide⟩).lower ∧ (cell12529 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12529 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12529 ⟨31,by decide⟩).lower ∧ (cell12529 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12529 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12529 ⟨32,by decide⟩).lower ∧ (cell12529 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12529 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12529 ⟨33,by decide⟩).lower ∧ (cell12529 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12529 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12529 ⟨34,by decide⟩).lower ∧ (cell12529 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12529 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12529 ⟨35,by decide⟩).lower ∧ (cell12529 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12529 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12529 ⟨36,by decide⟩).lower ∧ (cell12529 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12529 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12529 ⟨37,by decide⟩).lower ∧ (cell12529 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12529 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12529 ⟨38,by decide⟩).lower ∧ (cell12529 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12529 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12529 ⟨39,by decide⟩).lower ∧ (cell12529 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12529 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12529 ⟨40,by decide⟩).lower ∧ (cell12529 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12529 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12529 ⟨41,by decide⟩).lower ∧ (cell12529 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12529 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12529 ⟨42,by decide⟩).lower ∧ (cell12529 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12529 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12529 ⟨43,by decide⟩).lower ∧ (cell12529 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12529 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12529 ⟨44,by decide⟩).lower ∧ (cell12529 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12529 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12529 ⟨45,by decide⟩).lower ∧ (cell12529 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12529 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12529 ⟨46,by decide⟩).lower ∧ (cell12529 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12529 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12529 ⟨47,by decide⟩).lower ∧ (cell12529 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12529 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12529 ⟨48,by decide⟩).lower ∧ (cell12529 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12529 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12529 ⟨49,by decide⟩).lower ∧ (cell12529 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12529 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12529 ⟨50,by decide⟩).lower ∧ (cell12529 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12529 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12529 ⟨51,by decide⟩).lower ∧ (cell12529 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12529 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12529 ⟨52,by decide⟩).lower ∧ (cell12529 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12529 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12529 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12529 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12529,cell12529,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12529 i).lower ∧
    (cell12529 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12529 i).upper ≤ (0.532 : ℝ) ∧
    (cell12529 i).centre ≤ (0.1 : ℝ) ∧ (cell12529 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12529 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12529 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12529

/-! The local source numeric instances at 12529 have no network premises. -/
namespace BstLean.Part269.N12529
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12529)
open BstLean.Part268 (cell12529)

noncomputable def sourceNumerics12529 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12529 (cell12529 i)
      scalarRow12529.M scalarRow12529.H scalarRow12529.xi := by
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
    energy_allowance := scalarRow12529.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12529]
    centre_nonneg := (scalarRow12529.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12529])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12529
/-! Actual 12530 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12530 ≤ (1.036053466098 : ℝ) := by
  have hr : (111.937482551645 : ℝ) ≤ √(12530 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.937482551645 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12530 12530 (11 / 1000) ≤
    (0.008539472723 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12530) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.937482551645 : ℝ) ≤ √(12530 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12530)
  have hdiv : K / √(12530 : ℝ) ≤ K / 111.937482551645 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.937482551645 ≤ (0.008539472723 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12530.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12530 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12530 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12530 := gPlus_lower 12530
end BstLean.Part269.N12530

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12530
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036053466097 : ℝ) ≤ wn 12530 := by
  have hn : √(12530 : ℝ) ≤ 111.937482551646 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12530 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.937482551646 ≤ 2 / √(12530 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255358447 : ℝ) ≤ rhoBar 12530 BstLean.Part154.csC ∧
    rhoBar 12530 BstLean.Part154.csC ≤ 0.000255358842 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036053466097 : ℝ) / (1.295212 * 12530) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036053466098 : ℝ) / (1.29521 * 12530) := by gcongr
      _ ≤ (0.000255358842 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12530 BstLean.Part154.csC) ≤ 0.001021500577 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12530 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) ≤ 0.000195044932 ∧
    cc1 (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) ≤ 0.000124108359 ∧
    cc2 (rhoBar 12530 BstLean.Part154.csC) ≤ 0.000072045822 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12530 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12530 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12530 BstLean.Part154.csC * nuR (rhoBar 12530 BstLean.Part154.csC)) ≤ 0.000510733986 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255358842 : ℝ) * 0.001021500577 := by gcongr
      _ ≤ (0.000510733986 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12530 BstLean.Part154.csC) * nuR (rhoBar 12530 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021500577 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12530 BstLean.Part154.csC) * rhoBar 12530 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255358842 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255358842 / 2 + 0.399 * 0.001021500577 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195044932 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510733986 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124108359 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255358842 / 1.414213562 := by gcongr
      _ ≤ (0.000072045822 : ℝ) := by norm_num

end BstLean.Part269.N12530

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12530
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) ≤ 1.64288E-7 := by
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12530 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12530 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12530 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195044932 : ℝ) ^ 2 + 0.000124108359 ^ 2 + 3 * 0.000072045822 ^ 2 +
        2 * 0.797885 * 0.000195044932 * 0.000124108359 + 2 * 0.000195044932 * 0.000072045822 +
        4 * 0.797885 * 0.000124108359 * 0.000072045822 := by gcongr
    _ ≤ (1.64288E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12530 BstLean.Part154.csC Θ ≤ 0.002666231000 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12530 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12530 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12530 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036053466098 * 1.64288E-7 / (0.000255358447 : ℝ) := by gcongr
    _ ≤ 0.002666231000 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12530 BstLean.Part154.csC Θ ≤ 0.002959013615 + 0.000673710434 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12530 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12530 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036053466098 : ℝ) * ((2 * Θ * 0.000255358842 +
        (6863 / 10000) * 0.000255358842 * 12530 * 0.001021500577) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002959013615 + 0.000673710434 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12530 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12530 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12530 0.011 Θ ∧ gammaRatio 12530 0.011 Θ ≤ 0.000087785767 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12530 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036053466098 : ℝ) * 0.525 / ((1 - 0.011) * 12530) := by gcongr
      _ ≤ (0.000087785767 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12530 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12530 0.011 Θ) :=
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
    badAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12530 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12530 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12530 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12530 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12530 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12530 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12530 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12530 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12530 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12530 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036053466098 : ℝ) * 12530 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003702056285 + 0.003339941434 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12530

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12530
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12530 BstLean.Part154.csC) (piBar (rhoBar 12530 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12530 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12530 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12530 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12530 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12530 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12530 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12530 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12530 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12530 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12530 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052843025822 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12530) ≤ 0.010668790774 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12530 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036053466098)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010668790774 + 2 * 0.737676 / 12530) := by gcongr
    _ ≤ (0.052843025822 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12530 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12530

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12530
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495776081 : ℝ) ≤ plow 12530 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12530) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962125538)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399771275) : eMP 12530 0.011 xi bn ≤ 0.001204832744 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12530 : ℝ) * (1 - 0.011))) ≤ 0.000595703042 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399771275 / (12530 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595703042 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595703042 : ℝ) + 3.141593 * 0.052962125538 / (12530 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204832744 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962125538)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399771275) : PiBarMP 12530 12 0.011 xi bn ≤ 0.162352419340 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12530 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037413517277 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.320123966873 : ℝ) ≤ √((12530 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.937482551645 : ℝ) ≤ √(12530 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12530) ≤ 0.124465978198 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037413517277 + 0.052962125538 * 1.772454 / (2 * (111.320123966873 : ℝ))) * (1 + 0.001204832744) +
        8 / (12530 * 111.937482551645) + 0.124465978198 := by gcongr
    _ ≤ (0.162352419340 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962125538)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399771275) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282978041711) :
    parallelOracle 12530 0.011 xi bn cd ≤ 0.163356705006 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12530 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12530 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495776081 : ℝ) ≤ plow 12530 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.937482551645 : ℝ) ≤ √(12530 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282978041711 : ℝ) / (2 * 0.560495776081 * 111.937482551645)) * 0.162352419340 +
        0.282978041711 ^ 2 / (2 * 0.560495776081 * 111.937482551645) := by gcongr
    _ ≤ (0.163356705006 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052962125538) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399771275)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282978041711) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12530 12530 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495776081 : ℝ) ≤ plow 12530 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.937482551645 : ℝ) ≤ √(12530 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12530 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12530 Θ 1.22 ≤ 0.011846795817 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.937482551645 := by gcongr <;> linarith
      _ ≤ (0.011846795817 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12530 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12530 12530 0.011 ≤ 0.008539472723 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12530 12530 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12530 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12530 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12530 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12530 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163356705006 + 0.011846795817 + (0.008539472723 : ℝ) *
        (1 + 2 * (0.282978041711 + 0.011846795817) / (0.560495776081 * 111.937482551645))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12530]

end BstLean.Part269.N12530

/-! The original eight local profiles supply actual 12530 moment certificates. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12530 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052962125538 ∧
    0 ≤ bN 12530 BstLean.Part154.csC (groupTheta g) ∧ bN 12530 BstLean.Part154.csC (groupTheta g) ≤ 0.001399771275 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12530 12530 0.011
      (momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12530 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12530 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12530 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230135015889 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12530 0.011
      (momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12530 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12530
/-! The actual computed-centre upper energy formula at 12530. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12530

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12530)
open BstLean.Part268 (cell12530)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086002639908
  | 2 => 0.086955190518
  | 3 => 0.087907372186
  | 4 => 0.088860941890
  | 5 => 0.089818012788
  | 6 => 0.090781105540
  | 7 => 0.091753204169
  | 8 => 0.092737816446
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12530 12530 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12530 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12530

/-! Actual upper energy certificates on all 43 source endpoints at 12530. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12530)
open BstLean.Part268 (cell12530)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12530 (gMinus 12530) (1 - (cell12530 i).lower) ≤ 1 ∧
    energyUpper 12530 (gMinus 12530) (BstLean.Part211.gPlus 12530)
      (finiteEnergy 12530 12530 0.011) (1 - (cell12530 i).lower) ≤
      (cell12530 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨10,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨11,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨12,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨13,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨14,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨15,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨16,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨17,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨18,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨19,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨20,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨21,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨22,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨23,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨24,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨25,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨26,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨27,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨28,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨29,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨30,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨31,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨32,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨33,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨34,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨35,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨36,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨37,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨38,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨39,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨40,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨41,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨42,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨43,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨44,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨45,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨46,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨47,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨48,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨49,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨50,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨51,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12530) (by norm_num)
        (q := 1 - (cell12530 ⟨52,by decide⟩).lower)
        (by norm_num [cell12530]) (by norm_num [cell12530])
      exact ⟨E.1,E.2.trans (by norm_num [cell12530])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12530

/-! Source-cell containment and simple scalar guards at 12530. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12530)
open BstLean.Part268 (cell12530)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12530 ⟨10,by decide⟩).lower ∧ (cell12530 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12530 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12530 ⟨11,by decide⟩).lower ∧ (cell12530 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12530 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12530 ⟨12,by decide⟩).lower ∧ (cell12530 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12530 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12530 ⟨13,by decide⟩).lower ∧ (cell12530 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12530 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12530 ⟨14,by decide⟩).lower ∧ (cell12530 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12530 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12530 ⟨15,by decide⟩).lower ∧ (cell12530 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12530 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12530 ⟨16,by decide⟩).lower ∧ (cell12530 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12530 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12530 ⟨17,by decide⟩).lower ∧ (cell12530 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12530 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12530 ⟨18,by decide⟩).lower ∧ (cell12530 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12530 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12530 ⟨19,by decide⟩).lower ∧ (cell12530 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12530 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12530 ⟨20,by decide⟩).lower ∧ (cell12530 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12530 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12530 ⟨21,by decide⟩).lower ∧ (cell12530 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12530 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12530 ⟨22,by decide⟩).lower ∧ (cell12530 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12530 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12530 ⟨23,by decide⟩).lower ∧ (cell12530 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12530 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12530 ⟨24,by decide⟩).lower ∧ (cell12530 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12530 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12530 ⟨25,by decide⟩).lower ∧ (cell12530 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12530 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12530 ⟨26,by decide⟩).lower ∧ (cell12530 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12530 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12530 ⟨27,by decide⟩).lower ∧ (cell12530 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12530 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12530 ⟨28,by decide⟩).lower ∧ (cell12530 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12530 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12530 ⟨29,by decide⟩).lower ∧ (cell12530 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12530 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12530 ⟨30,by decide⟩).lower ∧ (cell12530 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12530 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12530 ⟨31,by decide⟩).lower ∧ (cell12530 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12530 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12530 ⟨32,by decide⟩).lower ∧ (cell12530 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12530 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12530 ⟨33,by decide⟩).lower ∧ (cell12530 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12530 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12530 ⟨34,by decide⟩).lower ∧ (cell12530 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12530 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12530 ⟨35,by decide⟩).lower ∧ (cell12530 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12530 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12530 ⟨36,by decide⟩).lower ∧ (cell12530 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12530 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12530 ⟨37,by decide⟩).lower ∧ (cell12530 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12530 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12530 ⟨38,by decide⟩).lower ∧ (cell12530 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12530 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12530 ⟨39,by decide⟩).lower ∧ (cell12530 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12530 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12530 ⟨40,by decide⟩).lower ∧ (cell12530 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12530 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12530 ⟨41,by decide⟩).lower ∧ (cell12530 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12530 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12530 ⟨42,by decide⟩).lower ∧ (cell12530 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12530 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12530 ⟨43,by decide⟩).lower ∧ (cell12530 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12530 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12530 ⟨44,by decide⟩).lower ∧ (cell12530 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12530 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12530 ⟨45,by decide⟩).lower ∧ (cell12530 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12530 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12530 ⟨46,by decide⟩).lower ∧ (cell12530 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12530 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12530 ⟨47,by decide⟩).lower ∧ (cell12530 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12530 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12530 ⟨48,by decide⟩).lower ∧ (cell12530 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12530 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12530 ⟨49,by decide⟩).lower ∧ (cell12530 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12530 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12530 ⟨50,by decide⟩).lower ∧ (cell12530 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12530 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12530 ⟨51,by decide⟩).lower ∧ (cell12530 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12530 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12530 ⟨52,by decide⟩).lower ∧ (cell12530 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12530 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12530 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12530 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12530,cell12530,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12530 i).lower ∧
    (cell12530 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12530 i).upper ≤ (0.532 : ℝ) ∧
    (cell12530 i).centre ≤ (0.1 : ℝ) ∧ (cell12530 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12530 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12530 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12530

/-! The local source numeric instances at 12530 have no network premises. -/
namespace BstLean.Part269.N12530
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12530)
open BstLean.Part268 (cell12530)

noncomputable def sourceNumerics12530 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12530 (cell12530 i)
      scalarRow12530.M scalarRow12530.H scalarRow12530.xi := by
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
    energy_allowance := scalarRow12530.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12530]
    centre_nonneg := (scalarRow12530.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12530])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12530
/-! Actual 12531 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12531 ≤ (1.036052014761 : ℝ) := by
  have hr : (111.941949241560 : ℝ) ≤ √(12531 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.941949241560 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12531 12531 (11 / 1000) ≤
    (0.008539131980 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12531) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.941949241560 : ℝ) ≤ √(12531 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12531)
  have hdiv : K / √(12531 : ℝ) ≤ K / 111.941949241560 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.941949241560 ≤ (0.008539131980 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12531.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12531 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12531 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12531 := gPlus_lower 12531
end BstLean.Part269.N12531

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12531
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036052014760 : ℝ) ≤ wn 12531 := by
  have hn : √(12531 : ℝ) ≤ 111.941949241561 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12531 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.941949241561 ≤ 2 / √(12531 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255337711 : ℝ) ≤ rhoBar 12531 BstLean.Part154.csC ∧
    rhoBar 12531 BstLean.Part154.csC ≤ 0.000255338106 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036052014760 : ℝ) / (1.295212 * 12531) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036052014761 : ℝ) / (1.29521 * 12531) := by gcongr
      _ ≤ (0.000255338106 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12531 BstLean.Part154.csC) ≤ 0.001021417622 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12531 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) ≤ 0.000195029092 ∧
    cc1 (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) ≤ 0.000124098281 ∧
    cc2 (rhoBar 12531 BstLean.Part154.csC) ≤ 0.000072039972 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12531 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12531 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12531 BstLean.Part154.csC * nuR (rhoBar 12531 BstLean.Part154.csC)) ≤ 0.000510692512 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255338106 : ℝ) * 0.001021417622 := by gcongr
      _ ≤ (0.000510692512 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12531 BstLean.Part154.csC) * nuR (rhoBar 12531 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021417622 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12531 BstLean.Part154.csC) * rhoBar 12531 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255338106 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255338106 / 2 + 0.399 * 0.001021417622 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195029092 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510692512 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124098281 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255338106 / 1.414213562 := by gcongr
      _ ≤ (0.000072039972 : ℝ) := by norm_num

end BstLean.Part269.N12531

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12531
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) ≤ 1.64261E-7 := by
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12531 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12531 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12531 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195029092 : ℝ) ^ 2 + 0.000124098281 ^ 2 + 3 * 0.000072039972 ^ 2 +
        2 * 0.797885 * 0.000195029092 * 0.000124098281 + 2 * 0.000195029092 * 0.000072039972 +
        4 * 0.797885 * 0.000124098281 * 0.000072039972 := by gcongr
    _ ≤ (1.64261E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12531 BstLean.Part154.csC Θ ≤ 0.002666005571 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12531 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12531 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12531 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036052014761 * 1.64261E-7 / (0.000255337711 : ℝ) := by gcongr
    _ ≤ 0.002666005571 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12531 BstLean.Part154.csC Θ ≤ 0.002958765026 + 0.000673654782 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12531 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12531 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036052014761 : ℝ) * ((2 * Θ * 0.000255338106 +
        (6863 / 10000) * 0.000255338106 * 12531 * 0.001021417622) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002958765026 + 0.000673654782 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12531 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12531 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12531 0.011 Θ ∧ gammaRatio 12531 0.011 Θ ≤ 0.000087778638 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12531 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036052014761 : ℝ) * 0.525 / ((1 - 0.011) * 12531) := by gcongr
      _ ≤ (0.000087778638 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12531 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12531 0.011 Θ) :=
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
    badAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12531 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12531 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12531 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12531 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12531 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12531 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12531 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12531 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12531 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12531 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036052014761 : ℝ) * 12531 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003701807696 + 0.003339660353 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12531

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12531
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12531 BstLean.Part154.csC) (piBar (rhoBar 12531 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12531 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12531 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12531 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12531 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12531 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12531 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12531 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12531 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12531 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12531 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052840894274 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12531) ≤ 0.010668365070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12531 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036052014761)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010668365070 + 2 * 0.737676 / 12531) := by gcongr
    _ ≤ (0.052840894274 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12531 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12531

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12531
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495822536 : ℝ) ≤ plow 12531 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12531) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961729382)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399652925) : eMP 12531 0.011 xi bn ≤ 0.001204733668 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12531 : ℝ) * (1 - 0.011))) ≤ 0.000595654090 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399652925 / (12531 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595654090 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595654090 : ℝ) + 3.141593 * 0.052961729382 / (12531 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204733668 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961729382)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399652925) : PiBarMP 12531 12 0.011 xi bn ≤ 0.162345844899 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12531 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037411935596 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.324566022060 : ℝ) ≤ √((12531 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.941949241560 : ℝ) ≤ √(12531 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12531) ≤ 0.124461011776 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037411935596 + 0.052961729382 * 1.772454 / (2 * (111.324566022060 : ℝ))) * (1 + 0.001204733668) +
        8 / (12531 * 111.941949241560) + 0.124461011776 := by gcongr
    _ ≤ (0.162345844899 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961729382)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399652925) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282975049458) :
    parallelOracle 12531 0.011 xi bn cd ≤ 0.163350058217 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12531 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12531 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495822536 : ℝ) ≤ plow 12531 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.941949241560 : ℝ) ≤ √(12531 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282975049458 : ℝ) / (2 * 0.560495822536 * 111.941949241560)) * 0.162345844899 +
        0.282975049458 ^ 2 / (2 * 0.560495822536 * 111.941949241560) := by gcongr
    _ ≤ (0.163350058217 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961729382) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399652925)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282975049458) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12531 12531 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495822536 : ℝ) ≤ plow 12531 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.941949241560 : ℝ) ≤ √(12531 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12531 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12531 Θ 1.22 ≤ 0.011846323108 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.941949241560 := by gcongr <;> linarith
      _ ≤ (0.011846323108 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12531 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12531 12531 0.011 ≤ 0.008539131980 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12531 12531 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12531 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12531 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12531 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12531 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163350058217 + 0.011846323108 + (0.008539131980 : ℝ) *
        (1 + 2 * (0.282975049458 + 0.011846323108) / (0.560495822536 * 111.941949241560))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12531]

end BstLean.Part269.N12531

/-! The original eight local profiles supply actual 12531 moment certificates. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12531 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052961729382 ∧
    0 ≤ bN 12531 BstLean.Part154.csC (groupTheta g) ∧ bN 12531 BstLean.Part154.csC (groupTheta g) ≤ 0.001399652925 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12531 12531 0.011
      (momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12531 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12531 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12531 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230134155184 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12531 0.011
      (momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12531 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12531
/-! The actual computed-centre upper energy formula at 12531. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12531

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12531)
open BstLean.Part268 (cell12531)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085999522895
  | 2 => 0.086952011489
  | 3 => 0.087904121346
  | 4 => 0.088857607245
  | 5 => 0.089814579768
  | 6 => 0.090777556576
  | 7 => 0.091749518222
  | 8 => 0.092733968490
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12531 12531 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12531 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12531

/-! Actual upper energy certificates on all 43 source endpoints at 12531. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12531)
open BstLean.Part268 (cell12531)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12531 (gMinus 12531) (1 - (cell12531 i).lower) ≤ 1 ∧
    energyUpper 12531 (gMinus 12531) (BstLean.Part211.gPlus 12531)
      (finiteEnergy 12531 12531 0.011) (1 - (cell12531 i).lower) ≤
      (cell12531 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨10,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨11,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨12,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨13,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨14,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨15,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨16,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨17,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨18,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨19,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨20,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨21,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨22,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨23,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨24,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨25,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨26,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨27,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨28,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨29,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨30,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨31,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨32,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨33,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨34,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨35,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨36,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨37,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨38,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨39,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨40,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨41,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨42,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨43,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨44,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨45,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨46,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨47,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨48,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨49,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨50,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨51,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12531) (by norm_num)
        (q := 1 - (cell12531 ⟨52,by decide⟩).lower)
        (by norm_num [cell12531]) (by norm_num [cell12531])
      exact ⟨E.1,E.2.trans (by norm_num [cell12531])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12531

/-! Source-cell containment and simple scalar guards at 12531. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12531)
open BstLean.Part268 (cell12531)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12531 ⟨10,by decide⟩).lower ∧ (cell12531 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12531 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12531 ⟨11,by decide⟩).lower ∧ (cell12531 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12531 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12531 ⟨12,by decide⟩).lower ∧ (cell12531 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12531 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12531 ⟨13,by decide⟩).lower ∧ (cell12531 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12531 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12531 ⟨14,by decide⟩).lower ∧ (cell12531 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12531 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12531 ⟨15,by decide⟩).lower ∧ (cell12531 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12531 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12531 ⟨16,by decide⟩).lower ∧ (cell12531 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12531 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12531 ⟨17,by decide⟩).lower ∧ (cell12531 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12531 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12531 ⟨18,by decide⟩).lower ∧ (cell12531 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12531 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12531 ⟨19,by decide⟩).lower ∧ (cell12531 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12531 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12531 ⟨20,by decide⟩).lower ∧ (cell12531 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12531 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12531 ⟨21,by decide⟩).lower ∧ (cell12531 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12531 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12531 ⟨22,by decide⟩).lower ∧ (cell12531 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12531 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12531 ⟨23,by decide⟩).lower ∧ (cell12531 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12531 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12531 ⟨24,by decide⟩).lower ∧ (cell12531 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12531 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12531 ⟨25,by decide⟩).lower ∧ (cell12531 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12531 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12531 ⟨26,by decide⟩).lower ∧ (cell12531 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12531 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12531 ⟨27,by decide⟩).lower ∧ (cell12531 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12531 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12531 ⟨28,by decide⟩).lower ∧ (cell12531 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12531 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12531 ⟨29,by decide⟩).lower ∧ (cell12531 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12531 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12531 ⟨30,by decide⟩).lower ∧ (cell12531 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12531 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12531 ⟨31,by decide⟩).lower ∧ (cell12531 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12531 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12531 ⟨32,by decide⟩).lower ∧ (cell12531 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12531 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12531 ⟨33,by decide⟩).lower ∧ (cell12531 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12531 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12531 ⟨34,by decide⟩).lower ∧ (cell12531 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12531 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12531 ⟨35,by decide⟩).lower ∧ (cell12531 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12531 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12531 ⟨36,by decide⟩).lower ∧ (cell12531 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12531 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12531 ⟨37,by decide⟩).lower ∧ (cell12531 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12531 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12531 ⟨38,by decide⟩).lower ∧ (cell12531 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12531 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12531 ⟨39,by decide⟩).lower ∧ (cell12531 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12531 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12531 ⟨40,by decide⟩).lower ∧ (cell12531 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12531 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12531 ⟨41,by decide⟩).lower ∧ (cell12531 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12531 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12531 ⟨42,by decide⟩).lower ∧ (cell12531 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12531 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12531 ⟨43,by decide⟩).lower ∧ (cell12531 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12531 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12531 ⟨44,by decide⟩).lower ∧ (cell12531 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12531 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12531 ⟨45,by decide⟩).lower ∧ (cell12531 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12531 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12531 ⟨46,by decide⟩).lower ∧ (cell12531 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12531 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12531 ⟨47,by decide⟩).lower ∧ (cell12531 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12531 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12531 ⟨48,by decide⟩).lower ∧ (cell12531 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12531 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12531 ⟨49,by decide⟩).lower ∧ (cell12531 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12531 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12531 ⟨50,by decide⟩).lower ∧ (cell12531 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12531 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12531 ⟨51,by decide⟩).lower ∧ (cell12531 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12531 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12531 ⟨52,by decide⟩).lower ∧ (cell12531 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12531 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12531 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12531 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12531,cell12531,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12531 i).lower ∧
    (cell12531 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12531 i).upper ≤ (0.532 : ℝ) ∧
    (cell12531 i).centre ≤ (0.1 : ℝ) ∧ (cell12531 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12531 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12531 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12531

/-! The local source numeric instances at 12531 have no network premises. -/
namespace BstLean.Part269.N12531
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12531)
open BstLean.Part268 (cell12531)

noncomputable def sourceNumerics12531 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12531 (cell12531 i)
      scalarRow12531.M scalarRow12531.H scalarRow12531.xi := by
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
    energy_allowance := scalarRow12531.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12531]
    centre_nonneg := (scalarRow12531.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12531])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12531
/-! Actual 12532 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12532 ≤ (1.036050563599 : ℝ) := by
  have hr : (111.946415753252 : ℝ) ≤ √(12532 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.946415753252 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12532 12532 (11 / 1000) ≤
    (0.008538791278 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12532) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.946415753252 : ℝ) ≤ √(12532 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12532)
  have hdiv : K / √(12532 : ℝ) ≤ K / 111.946415753252 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.946415753252 ≤ (0.008538791278 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12532.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12532 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12532 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12532 := gPlus_lower 12532
end BstLean.Part269.N12532

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12532
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036050563598 : ℝ) ≤ wn 12532 := by
  have hn : √(12532 : ℝ) ≤ 111.946415753253 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12532 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.946415753253 ≤ 2 / √(12532 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255316978 : ℝ) ≤ rhoBar 12532 BstLean.Part154.csC ∧
    rhoBar 12532 BstLean.Part154.csC ≤ 0.000255317374 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036050563598 : ℝ) / (1.295212 * 12532) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036050563599 : ℝ) / (1.29521 * 12532) := by gcongr
      _ ≤ (0.000255317374 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12532 BstLean.Part154.csC) ≤ 0.001021334683 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12532 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) ≤ 0.000195013256 ∧
    cc1 (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) ≤ 0.000124088204 ∧
    cc2 (rhoBar 12532 BstLean.Part154.csC) ≤ 0.000072034122 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12532 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12532 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12532 BstLean.Part154.csC * nuR (rhoBar 12532 BstLean.Part154.csC)) ≤ 0.000510651045 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255317374 : ℝ) * 0.001021334683 := by gcongr
      _ ≤ (0.000510651045 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12532 BstLean.Part154.csC) * nuR (rhoBar 12532 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021334683 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12532 BstLean.Part154.csC) * rhoBar 12532 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255317374 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255317374 / 2 + 0.399 * 0.001021334683 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195013256 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510651045 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124088204 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255317374 / 1.414213562 := by gcongr
      _ ≤ (0.000072034122 : ℝ) := by norm_num

end BstLean.Part269.N12532

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12532
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) ≤ 1.64234E-7 := by
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12532 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12532 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12532 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195013256 : ℝ) ^ 2 + 0.000124088204 ^ 2 + 3 * 0.000072034122 ^ 2 +
        2 * 0.797885 * 0.000195013256 * 0.000124088204 + 2 * 0.000195013256 * 0.000072034122 +
        4 * 0.797885 * 0.000124088204 * 0.000072034122 := by gcongr
    _ ≤ (1.64234E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12532 BstLean.Part154.csC Θ ≤ 0.002665780077 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12532 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12532 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12532 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036050563599 * 1.64234E-7 / (0.000255316978 : ℝ) := by gcongr
    _ ≤ 0.002665780077 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12532 BstLean.Part154.csC Θ ≤ 0.002958516492 + 0.000673599142 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12532 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12532 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036050563599 : ℝ) * ((2 * Θ * 0.000255317374 +
        (6863 / 10000) * 0.000255317374 * 12532 * 0.001021334683) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002958516492 + 0.000673599142 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12532 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12532 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12532 0.011 Θ ∧ gammaRatio 12532 0.011 Θ ≤ 0.000087771511 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12532 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036050563599 : ℝ) * 0.525 / ((1 - 0.011) * 12532) := by gcongr
      _ ≤ (0.000087771511 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12532 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12532 0.011 Θ) :=
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
    badAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12532 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12532 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12532 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12532 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12532 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12532 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12532 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12532 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12532 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12532 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036050563599 : ℝ) * 12532 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003701559162 + 0.003339379219 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12532

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12532
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12532 BstLean.Part154.csC) (piBar (rhoBar 12532 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12532 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12532 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12532 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12532 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12532 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12532 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12532 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12532 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12532 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12532 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052838762979 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12532) ≤ 0.010667939416 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12532 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036050563599)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010667939416 + 2 * 0.737676 / 12532) := by gcongr
    _ ≤ (0.052838762979 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12532 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12532

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12532
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495868983 : ℝ) ≤ plow 12532 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12532) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961333252)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399534541) : eMP 12532 0.011 xi bn ≤ 0.001204634584 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12532 : ℝ) * (1 - 0.011))) ≤ 0.000595605134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399534541 / (12532 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595605134 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595605134 : ℝ) + 3.141593 * 0.052961333252 / (12532 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204634584 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961333252)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399534541) : PiBarMP 12532 12 0.011 xi bn ≤ 0.162339270533 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12532 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037410353394 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.329007900007 : ℝ) ≤ √((12532 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.946415753252 : ℝ) ≤ √(12532 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12532) ≤ 0.124456045949 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037410353394 + 0.052961333252 * 1.772454 / (2 * (111.329007900007 : ℝ))) * (1 + 0.001204634584) +
        8 / (12532 * 111.946415753252) + 0.124456045949 := by gcongr
    _ ≤ (0.162339270533 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961333252)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399534541) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282972057511) :
    parallelOracle 12532 0.011 xi bn cd ≤ 0.163343411512 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12532 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12532 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495868983 : ℝ) ≤ plow 12532 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.946415753252 : ℝ) ≤ √(12532 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282972057511 : ℝ) / (2 * 0.560495868983 * 111.946415753252)) * 0.162339270533 +
        0.282972057511 ^ 2 / (2 * 0.560495868983 * 111.946415753252) := by gcongr
    _ ≤ (0.163343411512 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052961333252) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399534541)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282972057511) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12532 12532 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495868983 : ℝ) ≤ plow 12532 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.946415753252 : ℝ) ≤ √(12532 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12532 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12532 Θ 1.22 ≤ 0.011845850456 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.946415753252 := by gcongr <;> linarith
      _ ≤ (0.011845850456 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12532 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12532 12532 0.011 ≤ 0.008538791278 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12532 12532 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12532 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12532 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12532 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12532 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163343411512 + 0.011845850456 + (0.008538791278 : ℝ) *
        (1 + 2 * (0.282972057511 + 0.011845850456) / (0.560495868983 * 111.946415753252))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12532]

end BstLean.Part269.N12532

/-! The original eight local profiles supply actual 12532 moment certificates. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12532 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052961333252 ∧
    0 ≤ bN 12532 BstLean.Part154.csC (groupTheta g) ∧ bN 12532 BstLean.Part154.csC (groupTheta g) ≤ 0.001399534541 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12532 12532 0.011
      (momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12532 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12532 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12532 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230133294532 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12532 0.011
      (momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12532 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12532
/-! The actual computed-centre upper energy formula at 12532. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12532

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12532)
open BstLean.Part268 (cell12532)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085996407174
  | 2 => 0.086948833808
  | 3 => 0.087900871921
  | 4 => 0.088854274099
  | 5 => 0.089811148349
  | 6 => 0.090774009338
  | 7 => 0.091745834152
  | 8 => 0.092730122590
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12532 12532 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12532 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12532

/-! Actual upper energy certificates on all 43 source endpoints at 12532. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12532)
open BstLean.Part268 (cell12532)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12532 (gMinus 12532) (1 - (cell12532 i).lower) ≤ 1 ∧
    energyUpper 12532 (gMinus 12532) (BstLean.Part211.gPlus 12532)
      (finiteEnergy 12532 12532 0.011) (1 - (cell12532 i).lower) ≤
      (cell12532 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨10,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨11,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨12,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨13,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨14,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨15,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨16,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨17,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨18,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨19,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨20,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨21,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨22,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨23,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨24,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨25,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨26,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨27,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨28,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨29,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨30,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨31,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨32,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨33,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨34,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨35,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨36,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨37,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨38,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨39,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨40,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨41,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨42,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨43,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨44,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨45,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨46,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨47,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨48,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨49,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨50,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨51,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12532) (by norm_num)
        (q := 1 - (cell12532 ⟨52,by decide⟩).lower)
        (by norm_num [cell12532]) (by norm_num [cell12532])
      exact ⟨E.1,E.2.trans (by norm_num [cell12532])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12532

/-! Source-cell containment and simple scalar guards at 12532. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12532)
open BstLean.Part268 (cell12532)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12532 ⟨10,by decide⟩).lower ∧ (cell12532 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12532 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12532 ⟨11,by decide⟩).lower ∧ (cell12532 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12532 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12532 ⟨12,by decide⟩).lower ∧ (cell12532 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12532 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12532 ⟨13,by decide⟩).lower ∧ (cell12532 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12532 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12532 ⟨14,by decide⟩).lower ∧ (cell12532 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12532 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12532 ⟨15,by decide⟩).lower ∧ (cell12532 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12532 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12532 ⟨16,by decide⟩).lower ∧ (cell12532 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12532 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12532 ⟨17,by decide⟩).lower ∧ (cell12532 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12532 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12532 ⟨18,by decide⟩).lower ∧ (cell12532 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12532 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12532 ⟨19,by decide⟩).lower ∧ (cell12532 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12532 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12532 ⟨20,by decide⟩).lower ∧ (cell12532 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12532 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12532 ⟨21,by decide⟩).lower ∧ (cell12532 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12532 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12532 ⟨22,by decide⟩).lower ∧ (cell12532 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12532 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12532 ⟨23,by decide⟩).lower ∧ (cell12532 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12532 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12532 ⟨24,by decide⟩).lower ∧ (cell12532 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12532 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12532 ⟨25,by decide⟩).lower ∧ (cell12532 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12532 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12532 ⟨26,by decide⟩).lower ∧ (cell12532 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12532 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12532 ⟨27,by decide⟩).lower ∧ (cell12532 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12532 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12532 ⟨28,by decide⟩).lower ∧ (cell12532 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12532 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12532 ⟨29,by decide⟩).lower ∧ (cell12532 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12532 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12532 ⟨30,by decide⟩).lower ∧ (cell12532 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12532 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12532 ⟨31,by decide⟩).lower ∧ (cell12532 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12532 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12532 ⟨32,by decide⟩).lower ∧ (cell12532 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12532 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12532 ⟨33,by decide⟩).lower ∧ (cell12532 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12532 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12532 ⟨34,by decide⟩).lower ∧ (cell12532 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12532 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12532 ⟨35,by decide⟩).lower ∧ (cell12532 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12532 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12532 ⟨36,by decide⟩).lower ∧ (cell12532 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12532 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12532 ⟨37,by decide⟩).lower ∧ (cell12532 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12532 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12532 ⟨38,by decide⟩).lower ∧ (cell12532 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12532 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12532 ⟨39,by decide⟩).lower ∧ (cell12532 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12532 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12532 ⟨40,by decide⟩).lower ∧ (cell12532 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12532 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12532 ⟨41,by decide⟩).lower ∧ (cell12532 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12532 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12532 ⟨42,by decide⟩).lower ∧ (cell12532 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12532 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12532 ⟨43,by decide⟩).lower ∧ (cell12532 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12532 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12532 ⟨44,by decide⟩).lower ∧ (cell12532 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12532 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12532 ⟨45,by decide⟩).lower ∧ (cell12532 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12532 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12532 ⟨46,by decide⟩).lower ∧ (cell12532 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12532 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12532 ⟨47,by decide⟩).lower ∧ (cell12532 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12532 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12532 ⟨48,by decide⟩).lower ∧ (cell12532 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12532 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12532 ⟨49,by decide⟩).lower ∧ (cell12532 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12532 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12532 ⟨50,by decide⟩).lower ∧ (cell12532 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12532 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12532 ⟨51,by decide⟩).lower ∧ (cell12532 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12532 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12532 ⟨52,by decide⟩).lower ∧ (cell12532 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12532 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12532 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12532 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12532,cell12532,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12532 i).lower ∧
    (cell12532 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12532 i).upper ≤ (0.532 : ℝ) ∧
    (cell12532 i).centre ≤ (0.1 : ℝ) ∧ (cell12532 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12532 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12532 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12532

/-! The local source numeric instances at 12532 have no network premises. -/
namespace BstLean.Part269.N12532
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12532)
open BstLean.Part268 (cell12532)

noncomputable def sourceNumerics12532 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12532 (cell12532 i)
      scalarRow12532.M scalarRow12532.H scalarRow12532.xi := by
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
    energy_allowance := scalarRow12532.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12532]
    centre_nonneg := (scalarRow12532.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12532])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12532
/-! Actual 12533 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12533 ≤ (1.036049112611 : ℝ) := by
  have hr : (111.950882086743 : ℝ) ≤ √(12533 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.950882086743 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12533 12533 (11 / 1000) ≤
    (0.008538450616 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12533) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.950882086743 : ℝ) ≤ √(12533 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12533)
  have hdiv : K / √(12533 : ℝ) ≤ K / 111.950882086743 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.950882086743 ≤ (0.008538450616 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12533.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12533 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12533 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12533 := gPlus_lower 12533
end BstLean.Part269.N12533

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12533
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036049112610 : ℝ) ≤ wn 12533 := by
  have hn : √(12533 : ℝ) ≤ 111.950882086744 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12533 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.950882086744 ≤ 2 / √(12533 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255296249 : ℝ) ≤ rhoBar 12533 BstLean.Part154.csC ∧
    rhoBar 12533 BstLean.Part154.csC ≤ 0.000255296645 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036049112610 : ℝ) / (1.295212 * 12533) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036049112611 : ℝ) / (1.29521 * 12533) := by gcongr
      _ ≤ (0.000255296645 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12533 BstLean.Part154.csC) ≤ 0.001021251757 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12533 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) ≤ 0.000194997423 ∧
    cc1 (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) ≤ 0.000124078129 ∧
    cc2 (rhoBar 12533 BstLean.Part154.csC) ≤ 0.000072028274 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12533 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12533 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12533 BstLean.Part154.csC * nuR (rhoBar 12533 BstLean.Part154.csC)) ≤ 0.000510609584 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255296645 : ℝ) * 0.001021251757 := by gcongr
      _ ≤ (0.000510609584 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12533 BstLean.Part154.csC) * nuR (rhoBar 12533 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021251757 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12533 BstLean.Part154.csC) * rhoBar 12533 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255296645 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255296645 / 2 + 0.399 * 0.001021251757 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194997423 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510609584 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124078129 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255296645 / 1.414213562 := by gcongr
      _ ≤ (0.000072028274 : ℝ) := by norm_num

end BstLean.Part269.N12533

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12533
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) ≤ 1.64207E-7 := by
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12533 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12533 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12533 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194997423 : ℝ) ^ 2 + 0.000124078129 ^ 2 + 3 * 0.000072028274 ^ 2 +
        2 * 0.797885 * 0.000194997423 * 0.000124078129 + 2 * 0.000194997423 * 0.000072028274 +
        4 * 0.797885 * 0.000124078129 * 0.000072028274 := by gcongr
    _ ≤ (1.64207E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12533 BstLean.Part154.csC Θ ≤ 0.002665554505 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12533 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12533 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12533 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036049112611 * 1.64207E-7 / (0.000255296249 : ℝ) := by gcongr
    _ ≤ 0.002665554505 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12533 BstLean.Part154.csC Θ ≤ 0.002958267995 + 0.000673543510 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12533 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12533 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036049112611 : ℝ) * ((2 * Θ * 0.000255296645 +
        (6863 / 10000) * 0.000255296645 * 12533 * 0.001021251757) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002958267995 + 0.000673543510 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12533 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12533 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12533 0.011 Θ ∧ gammaRatio 12533 0.011 Θ ≤ 0.000087764385 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12533 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036049112611 : ℝ) * 0.525 / ((1 - 0.011) * 12533) := by gcongr
      _ ≤ (0.000087764385 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12533 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12533 0.011 Θ) :=
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
    badAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12533 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12533 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12533 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12533 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12533 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12533 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12533 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12533 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12533 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12533 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036049112611 : ℝ) * 12533 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003701310665 + 0.003339098015 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12533

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12533
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12533 BstLean.Part154.csC) (piBar (rhoBar 12533 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12533 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12533 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12533 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12533 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12533 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12533 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12533 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12533 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12533 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12533 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052836631945 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12533) ≤ 0.010667513814 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12533 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036049112611)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010667513814 + 2 * 0.737676 / 12533) := by gcongr
    _ ≤ (0.052836631945 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12533 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12533

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12533
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495915423 : ℝ) ≤ plow 12533 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12533) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960937123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399416116) : eMP 12533 0.011 xi bn ≤ 0.001204535491 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12533 : ℝ) * (1 - 0.011))) ≤ 0.000595556173 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399416116 / (12533 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595556173 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595556173 : ℝ) + 3.141593 * 0.052960937123 / (12533 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204535491 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960937123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399416116) : PiBarMP 12533 12 0.011 xi bn ≤ 0.162332696147 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12533 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037408770576 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.333449600737 : ℝ) ≤ √((12533 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.950882086743 : ℝ) ≤ √(12533 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12533) ≤ 0.124451080716 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037408770576 + 0.052960937123 * 1.772454 / (2 * (111.333449600737 : ℝ))) * (1 + 0.001204535491) +
        8 / (12533 * 111.950882086743) + 0.124451080716 := by gcongr
    _ ≤ (0.162332696147 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960937123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399416116) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282969065824) :
    parallelOracle 12533 0.011 xi bn cd ≤ 0.163336764797 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12533 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12533 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495915423 : ℝ) ≤ plow 12533 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.950882086743 : ℝ) ≤ √(12533 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282969065824 : ℝ) / (2 * 0.560495915423 * 111.950882086743)) * 0.162332696147 +
        0.282969065824 ^ 2 / (2 * 0.560495915423 * 111.950882086743) := by gcongr
    _ ≤ (0.163336764797 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960937123) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399416116)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282969065824) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12533 12533 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495915423 : ℝ) ≤ plow 12533 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.950882086743 : ℝ) ≤ √(12533 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12533 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12533 Θ 1.22 ≤ 0.011845377860 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.950882086743 := by gcongr <;> linarith
      _ ≤ (0.011845377860 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12533 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12533 12533 0.011 ≤ 0.008538450616 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12533 12533 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12533 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12533 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12533 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12533 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163336764797 + 0.011845377860 + (0.008538450616 : ℝ) *
        (1 + 2 * (0.282969065824 + 0.011845377860) / (0.560495915423 * 111.950882086743))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12533]

end BstLean.Part269.N12533

/-! The original eight local profiles supply actual 12533 moment certificates. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12533 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052960937123 ∧
    0 ≤ bN 12533 BstLean.Part154.csC (groupTheta g) ∧ bN 12533 BstLean.Part154.csC (groupTheta g) ≤ 0.001399416116 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12533 12533 0.011
      (momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12533 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12533 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12533 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230132433879 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12533 0.011
      (momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12533 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12533
/-! The actual computed-centre upper energy formula at 12533. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12533

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12533)
open BstLean.Part268 (cell12533)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085993292743
  | 2 => 0.086945657471
  | 3 => 0.087897623910
  | 4 => 0.088850942450
  | 5 => 0.089807718530
  | 6 => 0.090770463824
  | 7 => 0.091742151956
  | 8 => 0.092726278744
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12533 12533 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12533 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12533

/-! Actual upper energy certificates on all 43 source endpoints at 12533. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12533)
open BstLean.Part268 (cell12533)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12533 (gMinus 12533) (1 - (cell12533 i).lower) ≤ 1 ∧
    energyUpper 12533 (gMinus 12533) (BstLean.Part211.gPlus 12533)
      (finiteEnergy 12533 12533 0.011) (1 - (cell12533 i).lower) ≤
      (cell12533 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨10,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨11,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨12,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨13,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨14,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨15,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨16,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨17,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨18,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨19,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨20,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨21,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨22,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨23,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨24,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨25,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨26,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨27,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨28,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨29,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨30,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨31,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨32,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨33,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨34,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨35,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨36,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨37,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨38,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨39,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨40,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨41,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨42,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨43,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨44,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨45,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨46,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨47,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨48,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨49,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨50,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨51,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12533) (by norm_num)
        (q := 1 - (cell12533 ⟨52,by decide⟩).lower)
        (by norm_num [cell12533]) (by norm_num [cell12533])
      exact ⟨E.1,E.2.trans (by norm_num [cell12533])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12533

/-! Source-cell containment and simple scalar guards at 12533. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12533)
open BstLean.Part268 (cell12533)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12533 ⟨10,by decide⟩).lower ∧ (cell12533 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12533 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12533 ⟨11,by decide⟩).lower ∧ (cell12533 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12533 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12533 ⟨12,by decide⟩).lower ∧ (cell12533 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12533 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12533 ⟨13,by decide⟩).lower ∧ (cell12533 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12533 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12533 ⟨14,by decide⟩).lower ∧ (cell12533 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12533 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12533 ⟨15,by decide⟩).lower ∧ (cell12533 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12533 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12533 ⟨16,by decide⟩).lower ∧ (cell12533 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12533 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12533 ⟨17,by decide⟩).lower ∧ (cell12533 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12533 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12533 ⟨18,by decide⟩).lower ∧ (cell12533 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12533 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12533 ⟨19,by decide⟩).lower ∧ (cell12533 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12533 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12533 ⟨20,by decide⟩).lower ∧ (cell12533 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12533 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12533 ⟨21,by decide⟩).lower ∧ (cell12533 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12533 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12533 ⟨22,by decide⟩).lower ∧ (cell12533 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12533 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12533 ⟨23,by decide⟩).lower ∧ (cell12533 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12533 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12533 ⟨24,by decide⟩).lower ∧ (cell12533 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12533 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12533 ⟨25,by decide⟩).lower ∧ (cell12533 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12533 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12533 ⟨26,by decide⟩).lower ∧ (cell12533 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12533 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12533 ⟨27,by decide⟩).lower ∧ (cell12533 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12533 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12533 ⟨28,by decide⟩).lower ∧ (cell12533 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12533 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12533 ⟨29,by decide⟩).lower ∧ (cell12533 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12533 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12533 ⟨30,by decide⟩).lower ∧ (cell12533 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12533 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12533 ⟨31,by decide⟩).lower ∧ (cell12533 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12533 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12533 ⟨32,by decide⟩).lower ∧ (cell12533 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12533 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12533 ⟨33,by decide⟩).lower ∧ (cell12533 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12533 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12533 ⟨34,by decide⟩).lower ∧ (cell12533 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12533 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12533 ⟨35,by decide⟩).lower ∧ (cell12533 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12533 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12533 ⟨36,by decide⟩).lower ∧ (cell12533 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12533 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12533 ⟨37,by decide⟩).lower ∧ (cell12533 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12533 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12533 ⟨38,by decide⟩).lower ∧ (cell12533 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12533 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12533 ⟨39,by decide⟩).lower ∧ (cell12533 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12533 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12533 ⟨40,by decide⟩).lower ∧ (cell12533 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12533 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12533 ⟨41,by decide⟩).lower ∧ (cell12533 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12533 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12533 ⟨42,by decide⟩).lower ∧ (cell12533 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12533 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12533 ⟨43,by decide⟩).lower ∧ (cell12533 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12533 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12533 ⟨44,by decide⟩).lower ∧ (cell12533 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12533 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12533 ⟨45,by decide⟩).lower ∧ (cell12533 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12533 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12533 ⟨46,by decide⟩).lower ∧ (cell12533 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12533 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12533 ⟨47,by decide⟩).lower ∧ (cell12533 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12533 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12533 ⟨48,by decide⟩).lower ∧ (cell12533 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12533 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12533 ⟨49,by decide⟩).lower ∧ (cell12533 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12533 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12533 ⟨50,by decide⟩).lower ∧ (cell12533 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12533 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12533 ⟨51,by decide⟩).lower ∧ (cell12533 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12533 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12533 ⟨52,by decide⟩).lower ∧ (cell12533 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12533 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12533 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12533 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12533,cell12533,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12533 i).lower ∧
    (cell12533 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12533 i).upper ≤ (0.532 : ℝ) ∧
    (cell12533 i).centre ≤ (0.1 : ℝ) ∧ (cell12533 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12533 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12533 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12533

/-! The local source numeric instances at 12533 have no network premises. -/
namespace BstLean.Part269.N12533
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12533)
open BstLean.Part268 (cell12533)

noncomputable def sourceNumerics12533 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12533 (cell12533 i)
      scalarRow12533.M scalarRow12533.H scalarRow12533.xi := by
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
    energy_allowance := scalarRow12533.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12533]
    centre_nonneg := (scalarRow12533.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12533])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12533
/-! Actual 12534 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12534 ≤ (1.036047661798 : ℝ) := by
  have hr : (111.955348242055 : ℝ) ≤ √(12534 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.955348242055 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12534 12534 (11 / 1000) ≤
    (0.008538109995 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12534) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.955348242055 : ℝ) ≤ √(12534 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12534)
  have hdiv : K / √(12534 : ℝ) ≤ K / 111.955348242055 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.955348242055 ≤ (0.008538109995 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12534.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12534 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12534 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12534 := gPlus_lower 12534
end BstLean.Part269.N12534

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12534
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036047661797 : ℝ) ≤ wn 12534 := by
  have hn : √(12534 : ℝ) ≤ 111.955348242056 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12534 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.955348242056 ≤ 2 / √(12534 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255275524 : ℝ) ≤ rhoBar 12534 BstLean.Part154.csC ∧
    rhoBar 12534 BstLean.Part154.csC ≤ 0.000255275919 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036047661797 : ℝ) / (1.295212 * 12534) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036047661798 : ℝ) / (1.29521 * 12534) := by gcongr
      _ ≤ (0.000255275919 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12534 BstLean.Part154.csC) ≤ 0.001021168842 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12534 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) ≤ 0.000194981591 ∧
    cc1 (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) ≤ 0.000124068056 ∧
    cc2 (rhoBar 12534 BstLean.Part154.csC) ≤ 0.000072022427 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12534 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12534 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12534 BstLean.Part154.csC * nuR (rhoBar 12534 BstLean.Part154.csC)) ≤ 0.000510568130 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255275919 : ℝ) * 0.001021168842 := by gcongr
      _ ≤ (0.000510568130 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12534 BstLean.Part154.csC) * nuR (rhoBar 12534 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021168842 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12534 BstLean.Part154.csC) * rhoBar 12534 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255275919 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255275919 / 2 + 0.399 * 0.001021168842 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194981591 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510568130 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124068056 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255275919 / 1.414213562 := by gcongr
      _ ≤ (0.000072022427 : ℝ) := by norm_num

end BstLean.Part269.N12534

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12534
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) ≤ 1.64181E-7 := by
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12534 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12534 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12534 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194981591 : ℝ) ^ 2 + 0.000124068056 ^ 2 + 3 * 0.000072022427 ^ 2 +
        2 * 0.797885 * 0.000194981591 * 0.000124068056 + 2 * 0.000194981591 * 0.000072022427 +
        4 * 0.797885 * 0.000124068056 * 0.000072022427 := by gcongr
    _ ≤ (1.64181E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12534 BstLean.Part154.csC Θ ≤ 0.002665345091 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12534 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12534 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12534 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036047661798 * 1.64181E-7 / (0.000255275524 : ℝ) := by gcongr
    _ ≤ 0.002665345091 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12534 BstLean.Part154.csC Θ ≤ 0.002958019527 + 0.000673487886 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12534 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12534 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036047661798 : ℝ) * ((2 * Θ * 0.000255275919 +
        (6863 / 10000) * 0.000255275919 * 12534 * 0.001021168842) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002958019527 + 0.000673487886 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12534 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12534 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12534 0.011 Θ ∧ gammaRatio 12534 0.011 Θ ≤ 0.000087757260 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12534 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036047661798 : ℝ) * 0.525 / ((1 - 0.011) * 12534) := by gcongr
      _ ≤ (0.000087757260 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12534 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12534 0.011 Θ) :=
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
    badAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12534 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12534 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12534 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12534 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12534 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12534 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12534 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12534 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12534 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12534 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036047661798 : ℝ) * 12534 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003701062197 + 0.003338832977 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12534

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12534
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12534 BstLean.Part154.csC) (piBar (rhoBar 12534 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12534 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12534 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12534 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12534 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12534 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12534 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12534 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12534 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12534 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12534 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052834501164 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12534) ≤ 0.010667088262 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12534 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036047661798)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010667088262 + 2 * 0.737676 / 12534) := by gcongr
    _ ≤ (0.052834501164 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12534 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12534

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12534
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560495961855 : ℝ) ≤ plow 12534 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12534) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960549510)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399306173) : eMP 12534 0.011 xi bn ≤ 0.001204440017 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12534 : ℝ) * (1 - 0.011))) ≤ 0.000595509021 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399306173 / (12534 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595509021 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595509021 : ℝ) + 3.141593 * 0.052960549510 / (12534 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204440017 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960549510)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399306173) : PiBarMP 12534 12 0.011 xi bn ≤ 0.162326236007 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12534 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037407301066 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.337891124270 : ℝ) ≤ √((12534 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.955348242055 : ℝ) ≤ √(12534 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12534) ≤ 0.124446116077 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037407301066 + 0.052960549510 * 1.772454 / (2 * (111.337891124270 : ℝ))) * (1 + 0.001204440017) +
        8 / (12534 * 111.955348242055) + 0.124446116077 := by gcongr
    _ ≤ (0.162326236007 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960549510)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399306173) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282966092890) :
    parallelOracle 12534 0.011 xi bn cd ≤ 0.163330232702 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12534 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12534 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560495961855 : ℝ) ≤ plow 12534 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.955348242055 : ℝ) ≤ √(12534 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282966092890 : ℝ) / (2 * 0.560495961855 * 111.955348242055)) * 0.162326236007 +
        0.282966092890 ^ 2 / (2 * 0.560495961855 * 111.955348242055) := by gcongr
    _ ≤ (0.163330232702 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960549510) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399306173)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282966092890) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12534 12534 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560495961855 : ℝ) ≤ plow 12534 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.955348242055 : ℝ) ≤ √(12534 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12534 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12534 Θ 1.22 ≤ 0.011844905321 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.955348242055 := by gcongr <;> linarith
      _ ≤ (0.011844905321 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12534 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12534 12534 0.011 ≤ 0.008538109995 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12534 12534 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12534 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12534 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12534 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12534 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163330232702 + 0.011844905321 + (0.008538109995 : ℝ) *
        (1 + 2 * (0.282966092890 + 0.011844905321) / (0.560495961855 * 111.955348242055))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12534]

end BstLean.Part269.N12534

/-! The original eight local profiles supply actual 12534 moment certificates. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12534 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052960549510 ∧
    0 ≤ bN 12534 BstLean.Part154.csC (groupTheta g) ∧ bN 12534 BstLean.Part154.csC (groupTheta g) ≤ 0.001399306173 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12534 12534 0.011
      (momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12534 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12534 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12534 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230131591726 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12534 0.011
      (momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12534 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12534
/-! The actual computed-centre upper energy formula at 12534. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12534

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12534)
open BstLean.Part268 (cell12534)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085990179600
  | 2 => 0.086942482478
  | 3 => 0.087894377311
  | 4 => 0.088847612298
  | 5 => 0.089804290310
  | 6 => 0.090766920033
  | 7 => 0.091738471631
  | 8 => 0.092722436950
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12534 12534 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12534 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12534

/-! Actual upper energy certificates on all 43 source endpoints at 12534. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12534)
open BstLean.Part268 (cell12534)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12534 (gMinus 12534) (1 - (cell12534 i).lower) ≤ 1 ∧
    energyUpper 12534 (gMinus 12534) (BstLean.Part211.gPlus 12534)
      (finiteEnergy 12534 12534 0.011) (1 - (cell12534 i).lower) ≤
      (cell12534 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨10,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨11,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨12,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨13,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨14,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨15,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨16,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨17,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨18,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨19,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨20,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨21,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨22,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨23,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨24,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨25,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨26,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨27,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨28,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨29,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨30,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨31,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨32,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨33,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨34,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨35,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨36,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨37,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨38,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨39,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨40,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨41,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨42,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨43,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨44,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨45,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨46,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨47,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨48,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨49,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨50,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨51,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12534) (by norm_num)
        (q := 1 - (cell12534 ⟨52,by decide⟩).lower)
        (by norm_num [cell12534]) (by norm_num [cell12534])
      exact ⟨E.1,E.2.trans (by norm_num [cell12534])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12534

/-! Source-cell containment and simple scalar guards at 12534. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12534)
open BstLean.Part268 (cell12534)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12534 ⟨10,by decide⟩).lower ∧ (cell12534 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12534 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12534 ⟨11,by decide⟩).lower ∧ (cell12534 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12534 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12534 ⟨12,by decide⟩).lower ∧ (cell12534 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12534 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12534 ⟨13,by decide⟩).lower ∧ (cell12534 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12534 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12534 ⟨14,by decide⟩).lower ∧ (cell12534 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12534 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12534 ⟨15,by decide⟩).lower ∧ (cell12534 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12534 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12534 ⟨16,by decide⟩).lower ∧ (cell12534 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12534 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12534 ⟨17,by decide⟩).lower ∧ (cell12534 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12534 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12534 ⟨18,by decide⟩).lower ∧ (cell12534 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12534 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12534 ⟨19,by decide⟩).lower ∧ (cell12534 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12534 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12534 ⟨20,by decide⟩).lower ∧ (cell12534 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12534 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12534 ⟨21,by decide⟩).lower ∧ (cell12534 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12534 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12534 ⟨22,by decide⟩).lower ∧ (cell12534 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12534 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12534 ⟨23,by decide⟩).lower ∧ (cell12534 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12534 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12534 ⟨24,by decide⟩).lower ∧ (cell12534 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12534 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12534 ⟨25,by decide⟩).lower ∧ (cell12534 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12534 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12534 ⟨26,by decide⟩).lower ∧ (cell12534 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12534 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12534 ⟨27,by decide⟩).lower ∧ (cell12534 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12534 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12534 ⟨28,by decide⟩).lower ∧ (cell12534 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12534 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12534 ⟨29,by decide⟩).lower ∧ (cell12534 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12534 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12534 ⟨30,by decide⟩).lower ∧ (cell12534 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12534 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12534 ⟨31,by decide⟩).lower ∧ (cell12534 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12534 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12534 ⟨32,by decide⟩).lower ∧ (cell12534 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12534 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12534 ⟨33,by decide⟩).lower ∧ (cell12534 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12534 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12534 ⟨34,by decide⟩).lower ∧ (cell12534 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12534 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12534 ⟨35,by decide⟩).lower ∧ (cell12534 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12534 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12534 ⟨36,by decide⟩).lower ∧ (cell12534 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12534 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12534 ⟨37,by decide⟩).lower ∧ (cell12534 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12534 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12534 ⟨38,by decide⟩).lower ∧ (cell12534 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12534 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12534 ⟨39,by decide⟩).lower ∧ (cell12534 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12534 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12534 ⟨40,by decide⟩).lower ∧ (cell12534 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12534 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12534 ⟨41,by decide⟩).lower ∧ (cell12534 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12534 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12534 ⟨42,by decide⟩).lower ∧ (cell12534 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12534 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12534 ⟨43,by decide⟩).lower ∧ (cell12534 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12534 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12534 ⟨44,by decide⟩).lower ∧ (cell12534 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12534 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12534 ⟨45,by decide⟩).lower ∧ (cell12534 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12534 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12534 ⟨46,by decide⟩).lower ∧ (cell12534 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12534 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12534 ⟨47,by decide⟩).lower ∧ (cell12534 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12534 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12534 ⟨48,by decide⟩).lower ∧ (cell12534 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12534 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12534 ⟨49,by decide⟩).lower ∧ (cell12534 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12534 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12534 ⟨50,by decide⟩).lower ∧ (cell12534 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12534 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12534 ⟨51,by decide⟩).lower ∧ (cell12534 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12534 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12534 ⟨52,by decide⟩).lower ∧ (cell12534 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12534 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12534 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12534 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12534,cell12534,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12534 i).lower ∧
    (cell12534 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12534 i).upper ≤ (0.532 : ℝ) ∧
    (cell12534 i).centre ≤ (0.1 : ℝ) ∧ (cell12534 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12534 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12534 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12534

/-! The local source numeric instances at 12534 have no network premises. -/
namespace BstLean.Part269.N12534
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12534)
open BstLean.Part268 (cell12534)

noncomputable def sourceNumerics12534 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12534 (cell12534 i)
      scalarRow12534.M scalarRow12534.H scalarRow12534.xi := by
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
    energy_allowance := scalarRow12534.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12534]
    centre_nonneg := (scalarRow12534.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12534])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12534
/-! Actual 12535 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12535 ≤ (1.036046211159 : ℝ) := by
  have hr : (111.959814219209 : ℝ) ≤ √(12535 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.959814219209 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12535 12535 (11 / 1000) ≤
    (0.008537769414 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12535) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.959814219209 : ℝ) ≤ √(12535 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12535)
  have hdiv : K / √(12535 : ℝ) ≤ K / 111.959814219209 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.959814219209 ≤ (0.008537769414 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12535.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12535 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12535 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12535 := gPlus_lower 12535
end BstLean.Part269.N12535

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12535
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036046211158 : ℝ) ≤ wn 12535 := by
  have hn : √(12535 : ℝ) ≤ 111.959814219210 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12535 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.959814219210 ≤ 2 / √(12535 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255254801 : ℝ) ≤ rhoBar 12535 BstLean.Part154.csC ∧
    rhoBar 12535 BstLean.Part154.csC ≤ 0.000255255196 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036046211158 : ℝ) / (1.295212 * 12535) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036046211159 : ℝ) / (1.29521 * 12535) := by gcongr
      _ ≤ (0.000255255196 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12535 BstLean.Part154.csC) ≤ 0.001021085940 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12535 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) ≤ 0.000194965762 ∧
    cc1 (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) ≤ 0.000124057984 ∧
    cc2 (rhoBar 12535 BstLean.Part154.csC) ≤ 0.000072016580 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12535 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12535 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12535 BstLean.Part154.csC * nuR (rhoBar 12535 BstLean.Part154.csC)) ≤ 0.000510526681 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255255196 : ℝ) * 0.001021085940 := by gcongr
      _ ≤ (0.000510526681 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12535 BstLean.Part154.csC) * nuR (rhoBar 12535 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021085940 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12535 BstLean.Part154.csC) * rhoBar 12535 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255255196 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255255196 / 2 + 0.399 * 0.001021085940 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194965762 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510526681 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124057984 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255255196 / 1.414213562 := by gcongr
      _ ≤ (0.000072016580 : ℝ) := by norm_num

end BstLean.Part269.N12535

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12535
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) ≤ 1.64154E-7 := by
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12535 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12535 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12535 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194965762 : ℝ) ^ 2 + 0.000124057984 ^ 2 + 3 * 0.000072016580 ^ 2 +
        2 * 0.797885 * 0.000194965762 * 0.000124057984 + 2 * 0.000194965762 * 0.000072016580 +
        4 * 0.797885 * 0.000124057984 * 0.000072016580 := by gcongr
    _ ≤ (1.64154E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12535 BstLean.Part154.csC Θ ≤ 0.002665119388 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12535 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12535 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12535 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036046211159 * 1.64154E-7 / (0.000255254801 : ℝ) := by gcongr
    _ ≤ 0.002665119388 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12535 BstLean.Part154.csC Θ ≤ 0.002957771096 + 0.000673432270 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12535 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12535 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036046211159 : ℝ) * ((2 * Θ * 0.000255255196 +
        (6863 / 10000) * 0.000255255196 * 12535 * 0.001021085940) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002957771096 + 0.000673432270 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12535 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12535 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12535 0.011 Θ ∧ gammaRatio 12535 0.011 Θ ≤ 0.000087750136 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12535 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036046211159 : ℝ) * 0.525 / ((1 - 0.011) * 12535) := by gcongr
      _ ≤ (0.000087750136 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12535 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12535 0.011 Θ) :=
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
    badAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12535 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12535 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12535 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12535 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12535 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12535 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12535 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12535 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12535 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12535 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036046211159 : ℝ) * 12535 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003700813766 + 0.003338551658 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12535

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12535
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12535 BstLean.Part154.csC) (piBar (rhoBar 12535 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12535 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12535 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12535 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12535 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12535 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12535 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12535 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12535 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12535 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12535 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052832370640 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12535) ≤ 0.010666662761 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12535 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036046211159)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010666662761 + 2 * 0.737676 / 12535) := by gcongr
    _ ≤ (0.052832370640 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12535 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12535

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12535
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496008280 : ℝ) ≤ plow 12535 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12535) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960153387)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399187679) : eMP 12535 0.011 xi bn ≤ 0.001204340910 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12535 : ℝ) * (1 - 0.011))) ≤ 0.000595460053 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399187679 / (12535 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595460053 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595460053 : ℝ) + 3.141593 * 0.052960153387 / (12535 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204340910 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960153387)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399187679) : PiBarMP 12535 12 0.011 xi bn ≤ 0.162319661763 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12535 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037405717197 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.342332470628 : ℝ) ≤ √((12535 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.959814219209 : ℝ) ≤ √(12535 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12535) ≤ 0.124441152033 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037405717197 + 0.052960153387 * 1.772454 / (2 * (111.342332470628 : ℝ))) * (1 + 0.001204340910) +
        8 / (12535 * 111.959814219209) + 0.124441152033 := by gcongr
    _ ≤ (0.162319661763 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960153387)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399187679) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282963101720) :
    parallelOracle 12535 0.011 xi bn cd ≤ 0.163323586148 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12535 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12535 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496008280 : ℝ) ≤ plow 12535 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.959814219209 : ℝ) ≤ √(12535 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282963101720 : ℝ) / (2 * 0.560496008280 * 111.959814219209)) * 0.162319661763 +
        0.282963101720 ^ 2 / (2 * 0.560496008280 * 111.959814219209) := by gcongr
    _ ≤ (0.163323586148 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052960153387) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399187679)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282963101720) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12535 12535 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496008280 : ℝ) ≤ plow 12535 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.959814219209 : ℝ) ≤ √(12535 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12535 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12535 Θ 1.22 ≤ 0.011844432838 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.959814219209 := by gcongr <;> linarith
      _ ≤ (0.011844432838 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12535 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12535 12535 0.011 ≤ 0.008537769414 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12535 12535 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12535 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12535 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12535 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12535 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163323586148 + 0.011844432838 + (0.008537769414 : ℝ) *
        (1 + 2 * (0.282963101720 + 0.011844432838) / (0.560496008280 * 111.959814219209))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12535]

end BstLean.Part269.N12535

/-! The original eight local profiles supply actual 12535 moment certificates. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12535 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052960153387 ∧
    0 ≤ bN 12535 BstLean.Part154.csC (groupTheta g) ∧ bN 12535 BstLean.Part154.csC (groupTheta g) ≤ 0.001399187679 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12535 12535 0.011
      (momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12535 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12535 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12535 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230130731080 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12535 0.011
      (momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12535 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12535
/-! The actual computed-centre upper energy formula at 12535. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12535

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12535)
open BstLean.Part268 (cell12535)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085987067744
  | 2 => 0.086939308828
  | 3 => 0.087891132123
  | 4 => 0.088844283639
  | 5 => 0.089800863686
  | 6 => 0.090763377961
  | 7 => 0.091734793177
  | 8 => 0.092718597206
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12535 12535 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12535 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12535

/-! Actual upper energy certificates on all 43 source endpoints at 12535. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12535)
open BstLean.Part268 (cell12535)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12535 (gMinus 12535) (1 - (cell12535 i).lower) ≤ 1 ∧
    energyUpper 12535 (gMinus 12535) (BstLean.Part211.gPlus 12535)
      (finiteEnergy 12535 12535 0.011) (1 - (cell12535 i).lower) ≤
      (cell12535 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨10,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨11,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨12,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨13,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨14,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨15,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨16,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨17,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨18,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨19,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨20,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨21,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨22,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨23,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨24,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨25,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨26,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨27,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨28,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨29,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨30,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨31,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨32,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨33,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨34,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨35,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨36,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨37,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨38,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨39,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨40,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨41,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨42,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨43,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨44,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨45,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨46,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨47,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨48,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨49,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨50,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨51,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12535) (by norm_num)
        (q := 1 - (cell12535 ⟨52,by decide⟩).lower)
        (by norm_num [cell12535]) (by norm_num [cell12535])
      exact ⟨E.1,E.2.trans (by norm_num [cell12535])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12535

/-! Source-cell containment and simple scalar guards at 12535. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12535)
open BstLean.Part268 (cell12535)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12535 ⟨10,by decide⟩).lower ∧ (cell12535 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12535 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12535 ⟨11,by decide⟩).lower ∧ (cell12535 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12535 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12535 ⟨12,by decide⟩).lower ∧ (cell12535 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12535 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12535 ⟨13,by decide⟩).lower ∧ (cell12535 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12535 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12535 ⟨14,by decide⟩).lower ∧ (cell12535 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12535 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12535 ⟨15,by decide⟩).lower ∧ (cell12535 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12535 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12535 ⟨16,by decide⟩).lower ∧ (cell12535 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12535 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12535 ⟨17,by decide⟩).lower ∧ (cell12535 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12535 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12535 ⟨18,by decide⟩).lower ∧ (cell12535 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12535 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12535 ⟨19,by decide⟩).lower ∧ (cell12535 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12535 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12535 ⟨20,by decide⟩).lower ∧ (cell12535 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12535 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12535 ⟨21,by decide⟩).lower ∧ (cell12535 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12535 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12535 ⟨22,by decide⟩).lower ∧ (cell12535 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12535 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12535 ⟨23,by decide⟩).lower ∧ (cell12535 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12535 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12535 ⟨24,by decide⟩).lower ∧ (cell12535 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12535 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12535 ⟨25,by decide⟩).lower ∧ (cell12535 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12535 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12535 ⟨26,by decide⟩).lower ∧ (cell12535 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12535 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12535 ⟨27,by decide⟩).lower ∧ (cell12535 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12535 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12535 ⟨28,by decide⟩).lower ∧ (cell12535 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12535 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12535 ⟨29,by decide⟩).lower ∧ (cell12535 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12535 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12535 ⟨30,by decide⟩).lower ∧ (cell12535 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12535 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12535 ⟨31,by decide⟩).lower ∧ (cell12535 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12535 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12535 ⟨32,by decide⟩).lower ∧ (cell12535 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12535 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12535 ⟨33,by decide⟩).lower ∧ (cell12535 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12535 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12535 ⟨34,by decide⟩).lower ∧ (cell12535 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12535 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12535 ⟨35,by decide⟩).lower ∧ (cell12535 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12535 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12535 ⟨36,by decide⟩).lower ∧ (cell12535 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12535 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12535 ⟨37,by decide⟩).lower ∧ (cell12535 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12535 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12535 ⟨38,by decide⟩).lower ∧ (cell12535 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12535 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12535 ⟨39,by decide⟩).lower ∧ (cell12535 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12535 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12535 ⟨40,by decide⟩).lower ∧ (cell12535 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12535 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12535 ⟨41,by decide⟩).lower ∧ (cell12535 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12535 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12535 ⟨42,by decide⟩).lower ∧ (cell12535 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12535 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12535 ⟨43,by decide⟩).lower ∧ (cell12535 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12535 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12535 ⟨44,by decide⟩).lower ∧ (cell12535 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12535 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12535 ⟨45,by decide⟩).lower ∧ (cell12535 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12535 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12535 ⟨46,by decide⟩).lower ∧ (cell12535 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12535 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12535 ⟨47,by decide⟩).lower ∧ (cell12535 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12535 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12535 ⟨48,by decide⟩).lower ∧ (cell12535 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12535 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12535 ⟨49,by decide⟩).lower ∧ (cell12535 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12535 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12535 ⟨50,by decide⟩).lower ∧ (cell12535 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12535 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12535 ⟨51,by decide⟩).lower ∧ (cell12535 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12535 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12535 ⟨52,by decide⟩).lower ∧ (cell12535 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12535 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12535 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12535 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12535,cell12535,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12535 i).lower ∧
    (cell12535 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12535 i).upper ≤ (0.532 : ℝ) ∧
    (cell12535 i).centre ≤ (0.1 : ℝ) ∧ (cell12535 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12535 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12535 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12535

/-! The local source numeric instances at 12535 have no network premises. -/
namespace BstLean.Part269.N12535
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12535)
open BstLean.Part268 (cell12535)

noncomputable def sourceNumerics12535 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12535 (cell12535 i)
      scalarRow12535.M scalarRow12535.H scalarRow12535.xi := by
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
    energy_allowance := scalarRow12535.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12535]
    centre_nonneg := (scalarRow12535.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12535])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12535
/-! Actual 12536 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12536 ≤ (1.036044760696 : ℝ) := by
  have hr : (111.964280018227 : ℝ) ≤ √(12536 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.964280018227 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12536 12536 (11 / 1000) ≤
    (0.008537428875 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12536) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.964280018227 : ℝ) ≤ √(12536 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12536)
  have hdiv : K / √(12536 : ℝ) ≤ K / 111.964280018227 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.964280018227 ≤ (0.008537428875 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12536.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12536 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12536 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12536 := gPlus_lower 12536
end BstLean.Part269.N12536

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12536
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036044760695 : ℝ) ≤ wn 12536 := by
  have hn : √(12536 : ℝ) ≤ 111.964280018228 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12536 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.964280018228 ≤ 2 / √(12536 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255234082 : ℝ) ≤ rhoBar 12536 BstLean.Part154.csC ∧
    rhoBar 12536 BstLean.Part154.csC ≤ 0.000255234477 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036044760695 : ℝ) / (1.295212 * 12536) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036044760696 : ℝ) / (1.29521 * 12536) := by gcongr
      _ ≤ (0.000255234477 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12536 BstLean.Part154.csC) ≤ 0.001021003053 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12536 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) ≤ 0.000194949936 ∧
    cc1 (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) ≤ 0.000124047914 ∧
    cc2 (rhoBar 12536 BstLean.Part154.csC) ≤ 0.000072010734 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12536 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12536 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12536 BstLean.Part154.csC * nuR (rhoBar 12536 BstLean.Part154.csC)) ≤ 0.000510485240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255234477 : ℝ) * 0.001021003053 := by gcongr
      _ ≤ (0.000510485240 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12536 BstLean.Part154.csC) * nuR (rhoBar 12536 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001021003053 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12536 BstLean.Part154.csC) * rhoBar 12536 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255234477 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255234477 / 2 + 0.399 * 0.001021003053 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194949936 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510485240 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124047914 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255234477 / 1.414213562 := by gcongr
      _ ≤ (0.000072010734 : ℝ) := by norm_num

end BstLean.Part269.N12536

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12536
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) ≤ 1.64128E-7 := by
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12536 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12536 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12536 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194949936 : ℝ) ^ 2 + 0.000124047914 ^ 2 + 3 * 0.000072010734 ^ 2 +
        2 * 0.797885 * 0.000194949936 * 0.000124047914 + 2 * 0.000194949936 * 0.000072010734 +
        4 * 0.797885 * 0.000124047914 * 0.000072010734 := by gcongr
    _ ≤ (1.64128E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12536 BstLean.Part154.csC Θ ≤ 0.002664909846 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12536 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12536 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12536 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036044760696 * 1.64128E-7 / (0.000255234082 : ℝ) := by gcongr
    _ ≤ 0.002664909846 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12536 BstLean.Part154.csC Θ ≤ 0.002957522718 + 0.000673376665 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12536 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12536 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036044760696 : ℝ) * ((2 * Θ * 0.000255234477 +
        (6863 / 10000) * 0.000255234477 * 12536 * 0.001021003053) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002957522718 + 0.000673376665 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12536 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12536 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12536 0.011 Θ ∧ gammaRatio 12536 0.011 Θ ≤ 0.000087743013 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12536 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036044760696 : ℝ) * 0.525 / ((1 - 0.011) * 12536) := by gcongr
      _ ≤ (0.000087743013 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12536 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12536 0.011 Θ) :=
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
    badAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12536 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12536 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12536 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12536 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12536 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12536 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12536 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12536 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12536 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12536 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036044760696 : ℝ) * 12536 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003700565388 + 0.003338286511 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12536

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12536
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12536 BstLean.Part154.csC) (piBar (rhoBar 12536 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12536 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12536 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12536 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12536 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12536 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12536 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12536 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12536 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12536 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12536 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052830240378 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12536) ≤ 0.010666237312 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12536 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036044760696)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010666237312 + 2 * 0.737676 / 12536) := by gcongr
    _ ≤ (0.052830240378 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12536 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12536

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12536
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496054698 : ℝ) ≤ plow 12536 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12536) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959765807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399077670) : eMP 12536 0.011 xi bn ≤ 0.001204245425 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12536 : ℝ) * (1 - 0.011))) ≤ 0.000595412895 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001399077670 / (12536 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595412895 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595412895 : ℝ) + 3.141593 * 0.052959765807 / (12536 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204245425 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959765807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399077670) : PiBarMP 12536 12 0.011 xi bn ≤ 0.162313201813 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12536 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037404246685 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.346773639832 : ℝ) ≤ √((12536 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.964280018227 : ℝ) ≤ √(12536 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12536) ≤ 0.124436188582 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037404246685 + 0.052959765807 * 1.772454 / (2 * (111.346773639832 : ℝ))) * (1 + 0.001204245425) +
        8 / (12536 * 111.964280018227) + 0.124436188582 := by gcongr
    _ ≤ (0.162313201813 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959765807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399077670) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282960129369) :
    parallelOracle 12536 0.011 xi bn cd ≤ 0.163317054262 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12536 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12536 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496054698 : ℝ) ≤ plow 12536 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.964280018227 : ℝ) ≤ √(12536 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282960129369 : ℝ) / (2 * 0.560496054698 * 111.964280018227)) * 0.162313201813 +
        0.282960129369 ^ 2 / (2 * 0.560496054698 * 111.964280018227) := by gcongr
    _ ≤ (0.163317054262 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959765807) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001399077670)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282960129369) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12536 12536 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496054698 : ℝ) ≤ plow 12536 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.964280018227 : ℝ) ≤ √(12536 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12536 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12536 Θ 1.22 ≤ 0.011843960412 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.964280018227 := by gcongr <;> linarith
      _ ≤ (0.011843960412 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12536 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12536 12536 0.011 ≤ 0.008537428875 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12536 12536 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12536 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12536 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12536 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12536 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163317054262 + 0.011843960412 + (0.008537428875 : ℝ) *
        (1 + 2 * (0.282960129369 + 0.011843960412) / (0.560496054698 * 111.964280018227))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12536]

end BstLean.Part269.N12536

/-! The original eight local profiles supply actual 12536 moment certificates. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12536 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052959765807 ∧
    0 ≤ bN 12536 BstLean.Part154.csC (groupTheta g) ∧ bN 12536 BstLean.Part154.csC (groupTheta g) ≤ 0.001399077670 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12536 12536 0.011
      (momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12536 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12536 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12536 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230129888991 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12536 0.011
      (momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12536 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12536
/-! The actual computed-centre upper energy formula at 12536. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12536

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12536)
open BstLean.Part268 (cell12536)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085983957175
  | 2 => 0.086936136519
  | 3 => 0.087887888343
  | 4 => 0.088840956474
  | 5 => 0.089797438657
  | 6 => 0.090759837609
  | 7 => 0.091731116591
  | 8 => 0.092714759508
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12536 12536 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12536 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12536

/-! Actual upper energy certificates on all 43 source endpoints at 12536. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12536)
open BstLean.Part268 (cell12536)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12536 (gMinus 12536) (1 - (cell12536 i).lower) ≤ 1 ∧
    energyUpper 12536 (gMinus 12536) (BstLean.Part211.gPlus 12536)
      (finiteEnergy 12536 12536 0.011) (1 - (cell12536 i).lower) ≤
      (cell12536 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨10,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨11,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨12,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨13,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨14,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨15,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨16,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨17,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨18,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨19,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨20,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨21,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨22,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨23,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨24,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨25,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨26,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨27,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨28,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨29,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨30,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨31,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨32,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨33,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨34,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨35,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨36,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨37,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨38,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨39,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨40,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨41,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨42,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨43,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨44,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨45,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨46,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨47,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨48,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨49,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨50,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨51,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12536) (by norm_num)
        (q := 1 - (cell12536 ⟨52,by decide⟩).lower)
        (by norm_num [cell12536]) (by norm_num [cell12536])
      exact ⟨E.1,E.2.trans (by norm_num [cell12536])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12536

/-! Source-cell containment and simple scalar guards at 12536. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12536)
open BstLean.Part268 (cell12536)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12536 ⟨10,by decide⟩).lower ∧ (cell12536 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12536 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12536 ⟨11,by decide⟩).lower ∧ (cell12536 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12536 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12536 ⟨12,by decide⟩).lower ∧ (cell12536 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12536 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12536 ⟨13,by decide⟩).lower ∧ (cell12536 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12536 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12536 ⟨14,by decide⟩).lower ∧ (cell12536 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12536 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12536 ⟨15,by decide⟩).lower ∧ (cell12536 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12536 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12536 ⟨16,by decide⟩).lower ∧ (cell12536 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12536 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12536 ⟨17,by decide⟩).lower ∧ (cell12536 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12536 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12536 ⟨18,by decide⟩).lower ∧ (cell12536 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12536 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12536 ⟨19,by decide⟩).lower ∧ (cell12536 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12536 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12536 ⟨20,by decide⟩).lower ∧ (cell12536 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12536 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12536 ⟨21,by decide⟩).lower ∧ (cell12536 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12536 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12536 ⟨22,by decide⟩).lower ∧ (cell12536 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12536 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12536 ⟨23,by decide⟩).lower ∧ (cell12536 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12536 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12536 ⟨24,by decide⟩).lower ∧ (cell12536 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12536 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12536 ⟨25,by decide⟩).lower ∧ (cell12536 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12536 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12536 ⟨26,by decide⟩).lower ∧ (cell12536 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12536 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12536 ⟨27,by decide⟩).lower ∧ (cell12536 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12536 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12536 ⟨28,by decide⟩).lower ∧ (cell12536 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12536 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12536 ⟨29,by decide⟩).lower ∧ (cell12536 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12536 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12536 ⟨30,by decide⟩).lower ∧ (cell12536 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12536 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12536 ⟨31,by decide⟩).lower ∧ (cell12536 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12536 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12536 ⟨32,by decide⟩).lower ∧ (cell12536 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12536 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12536 ⟨33,by decide⟩).lower ∧ (cell12536 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12536 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12536 ⟨34,by decide⟩).lower ∧ (cell12536 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12536 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12536 ⟨35,by decide⟩).lower ∧ (cell12536 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12536 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12536 ⟨36,by decide⟩).lower ∧ (cell12536 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12536 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12536 ⟨37,by decide⟩).lower ∧ (cell12536 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12536 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12536 ⟨38,by decide⟩).lower ∧ (cell12536 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12536 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12536 ⟨39,by decide⟩).lower ∧ (cell12536 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12536 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12536 ⟨40,by decide⟩).lower ∧ (cell12536 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12536 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12536 ⟨41,by decide⟩).lower ∧ (cell12536 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12536 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12536 ⟨42,by decide⟩).lower ∧ (cell12536 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12536 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12536 ⟨43,by decide⟩).lower ∧ (cell12536 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12536 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12536 ⟨44,by decide⟩).lower ∧ (cell12536 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12536 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12536 ⟨45,by decide⟩).lower ∧ (cell12536 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12536 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12536 ⟨46,by decide⟩).lower ∧ (cell12536 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12536 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12536 ⟨47,by decide⟩).lower ∧ (cell12536 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12536 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12536 ⟨48,by decide⟩).lower ∧ (cell12536 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12536 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12536 ⟨49,by decide⟩).lower ∧ (cell12536 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12536 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12536 ⟨50,by decide⟩).lower ∧ (cell12536 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12536 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12536 ⟨51,by decide⟩).lower ∧ (cell12536 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12536 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12536 ⟨52,by decide⟩).lower ∧ (cell12536 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12536 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12536 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12536 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12536,cell12536,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12536 i).lower ∧
    (cell12536 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12536 i).upper ≤ (0.532 : ℝ) ∧
    (cell12536 i).centre ≤ (0.1 : ℝ) ∧ (cell12536 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12536 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12536 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12536

/-! The local source numeric instances at 12536 have no network premises. -/
namespace BstLean.Part269.N12536
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12536)
open BstLean.Part268 (cell12536)

noncomputable def sourceNumerics12536 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12536 (cell12536 i)
      scalarRow12536.M scalarRow12536.H scalarRow12536.xi := by
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
    energy_allowance := scalarRow12536.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12536]
    centre_nonneg := (scalarRow12536.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12536])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12536
/-! Actual 12537 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12537 ≤ (1.036043310406 : ℝ) := by
  have hr : (111.968745639129 : ℝ) ≤ √(12537 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.968745639129 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12537 12537 (11 / 1000) ≤
    (0.008537088376 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12537) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.968745639129 : ℝ) ≤ √(12537 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12537)
  have hdiv : K / √(12537 : ℝ) ≤ K / 111.968745639129 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.968745639129 ≤ (0.008537088376 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12537.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12537 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12537 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12537 := gPlus_lower 12537
end BstLean.Part269.N12537

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12537
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036043310405 : ℝ) ≤ wn 12537 := by
  have hn : √(12537 : ℝ) ≤ 111.968745639130 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12537 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.968745639130 ≤ 2 / √(12537 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000255213366 : ℝ) ≤ rhoBar 12537 BstLean.Part154.csC ∧
    rhoBar 12537 BstLean.Part154.csC ≤ 0.000255213761 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036043310405 : ℝ) / (1.295212 * 12537) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036043310406 : ℝ) / (1.29521 * 12537) := by gcongr
      _ ≤ (0.000255213761 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12537 BstLean.Part154.csC) ≤ 0.001020920179 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12537 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) ≤ 0.000194934112 ∧
    cc1 (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) ≤ 0.000124037845 ∧
    cc2 (rhoBar 12537 BstLean.Part154.csC) ≤ 0.000072004890 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12537 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12537 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12537 BstLean.Part154.csC * nuR (rhoBar 12537 BstLean.Part154.csC)) ≤ 0.000510443806 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000255213761 : ℝ) * 0.001020920179 := by gcongr
      _ ≤ (0.000510443806 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12537 BstLean.Part154.csC) * nuR (rhoBar 12537 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001020920179 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12537 BstLean.Part154.csC) * rhoBar 12537 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000255213761 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000255213761 / 2 + 0.399 * 0.001020920179 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194934112 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000510443806 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124037845 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000255213761 / 1.414213562 := by gcongr
      _ ≤ (0.000072004890 : ℝ) := by norm_num

end BstLean.Part269.N12537

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12537
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) ≤ 1.64101E-7 := by
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12537 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12537 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12537 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194934112 : ℝ) ^ 2 + 0.000124037845 ^ 2 + 3 * 0.000072004890 ^ 2 +
        2 * 0.797885 * 0.000194934112 * 0.000124037845 + 2 * 0.000194934112 * 0.000072004890 +
        4 * 0.797885 * 0.000124037845 * 0.000072004890 := by gcongr
    _ ≤ (1.64101E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12537 BstLean.Part154.csC Θ ≤ 0.002664684001 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12537 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12537 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12537 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036043310406 * 1.64101E-7 / (0.000255213366 : ℝ) := by gcongr
    _ ≤ 0.002664684001 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12537 BstLean.Part154.csC Θ ≤ 0.002957274376 + 0.000673321068 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12537 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12537 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036043310406 : ℝ) * ((2 * Θ * 0.000255213761 +
        (6863 / 10000) * 0.000255213761 * 12537 * 0.001020920179) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002957274376 + 0.000673321068 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12537 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12537 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12537 0.011 Θ ∧ gammaRatio 12537 0.011 Θ ≤ 0.000087735892 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12537 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036043310406 : ℝ) * 0.525 / ((1 - 0.011) * 12537) := by gcongr
      _ ≤ (0.000087735892 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12537 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12537 0.011 Θ) :=
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
    badAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743042670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12537 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12537 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12537 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12537 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12537 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12537 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12537 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12537 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12537 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12537 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036043310406 : ℝ) * 12537 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743042670 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003700317046 + 0.003338005069 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12537

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12537
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12537 BstLean.Part154.csC) (piBar (rhoBar 12537 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12537 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12537 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12537 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12537 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12537 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12537 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12537 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12537 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12537 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12537 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052828110368 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12537) ≤ 0.010665811913 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12537 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036043310406)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010665811913 + 2 * 0.737676 / 12537) := by gcongr
    _ ≤ (0.052828110368 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12537 12 ≤ 0.0015 := by
  exact BstLean.Part269.S7.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12537

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12537
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496101108 : ℝ) ≤ plow 12537 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12537) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959369708)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398959101) : eMP 12537 0.011 xi bn ≤ 0.001204146301 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12537 : ℝ) * (1 - 0.011))) ≤ 0.000595363918 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001398959101 / (12537 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000595363918 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000595363918 : ℝ) + 3.141593 * 0.052959369708 / (12537 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001204146301 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959369708)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398959101) : PiBarMP 12537 12 0.011 xi bn ≤ 0.162306627627 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12537 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037402661684 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.351214631902 : ℝ) ≤ √((12537 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.968745639129 : ℝ) ≤ √(12537 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12537) ≤ 0.124431225725 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037402661684 + 0.052959369708 * 1.772454 / (2 * (111.351214631902 : ℝ))) * (1 + 0.001204146301) +
        8 / (12537 * 111.968745639129) + 0.124431225725 := by gcongr
    _ ≤ (0.162306627627 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959369708)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398959101) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282957138759) :
    parallelOracle 12537 0.011 xi bn cd ≤ 0.163310407785 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12537 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12537 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496101108 : ℝ) ≤ plow 12537 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.968745639129 : ℝ) ≤ √(12537 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282957138759 : ℝ) / (2 * 0.560496101108 * 111.968745639129)) * 0.162306627627 +
        0.282957138759 ^ 2 / (2 * 0.560496101108 * 111.968745639129) := by gcongr
    _ ≤ (0.163310407785 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052959369708) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001398959101)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282957138759) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12537 12537 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496101108 : ℝ) ≤ plow 12537 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.968745639129 : ℝ) ≤ √(12537 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12537 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12537 Θ 1.22 ≤ 0.011843488042 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.968745639129 := by gcongr <;> linarith
      _ ≤ (0.011843488042 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12537 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12537 12537 0.011 ≤ 0.008537088376 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12537 12537 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12537 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12537 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12537 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12537 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163310407785 + 0.011843488042 + (0.008537088376 : ℝ) *
        (1 + 2 * (0.282957138759 + 0.011843488042) / (0.560496101108 * 111.968745639129))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12537]

end BstLean.Part269.N12537

/-! The original eight local profiles supply actual 12537 moment certificates. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12537 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052959369708 ∧
    0 ≤ bN 12537 BstLean.Part154.csC (groupTheta g) ∧ bN 12537 BstLean.Part154.csC (groupTheta g) ≤ 0.001398959101 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12537 12537 0.011
      (momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12537 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12537 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12537 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230129028391 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12537 0.011
      (momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12537 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12537
/-! The actual computed-centre upper energy formula at 12537. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12537

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12537)
open BstLean.Part268 (cell12537)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085980847889
  | 2 => 0.086932965550
  | 3 => 0.087884645971
  | 4 => 0.088837630799
  | 5 => 0.089794015220
  | 6 => 0.090756298972
  | 7 => 0.091727441870
  | 8 => 0.092710923856
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12537 12537 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12537 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003703299838 + 0.003341313488 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S7.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S7.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12537

/-! Actual upper energy certificates on all 43 source endpoints at 12537. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12537)
open BstLean.Part268 (cell12537)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12537 (gMinus 12537) (1 - (cell12537 i).lower) ≤ 1 ∧
    energyUpper 12537 (gMinus 12537) (BstLean.Part211.gPlus 12537)
      (finiteEnergy 12537 12537 0.011) (1 - (cell12537 i).lower) ≤
      (cell12537 i).energy := by
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
      have E := BstLean.Part269.S7.uniformEnergy10 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨10,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy11 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨11,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy12 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨12,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy13 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨13,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy14 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨14,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy15 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨15,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy16 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨16,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy17 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨17,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy18 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨18,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy19 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨19,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy20 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨20,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy21 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨21,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy22 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨22,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy23 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨23,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy24 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨24,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy25 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨25,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy26 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨26,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy27 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨27,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy28 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨28,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy29 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨29,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy30 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨30,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy31 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨31,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy32 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨32,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy33 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨33,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy34 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨34,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy35 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨35,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy36 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨36,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy37 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨37,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy38 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨38,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy39 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨39,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy40 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨40,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy41 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨41,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy42 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨42,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy43 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨43,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy44 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨44,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy45 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨45,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy46 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨46,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy47 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨47,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy48 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨48,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy49 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨49,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy50 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨50,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy51 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨51,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S7.uniformEnergy52 (n := 12537) (by norm_num)
        (q := 1 - (cell12537 ⟨52,by decide⟩).lower)
        (by norm_num [cell12537]) (by norm_num [cell12537])
      exact ⟨E.1,E.2.trans (by norm_num [cell12537])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12537

/-! Source-cell containment and simple scalar guards at 12537. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12537)
open BstLean.Part268 (cell12537)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12537 ⟨10,by decide⟩).lower ∧ (cell12537 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12537 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12537 ⟨11,by decide⟩).lower ∧ (cell12537 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12537 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12537 ⟨12,by decide⟩).lower ∧ (cell12537 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12537 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12537 ⟨13,by decide⟩).lower ∧ (cell12537 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12537 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12537 ⟨14,by decide⟩).lower ∧ (cell12537 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12537 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12537 ⟨15,by decide⟩).lower ∧ (cell12537 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12537 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12537 ⟨16,by decide⟩).lower ∧ (cell12537 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12537 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12537 ⟨17,by decide⟩).lower ∧ (cell12537 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12537 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12537 ⟨18,by decide⟩).lower ∧ (cell12537 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12537 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12537 ⟨19,by decide⟩).lower ∧ (cell12537 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12537 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12537 ⟨20,by decide⟩).lower ∧ (cell12537 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12537 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12537 ⟨21,by decide⟩).lower ∧ (cell12537 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12537 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12537 ⟨22,by decide⟩).lower ∧ (cell12537 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12537 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12537 ⟨23,by decide⟩).lower ∧ (cell12537 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12537 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12537 ⟨24,by decide⟩).lower ∧ (cell12537 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12537 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12537 ⟨25,by decide⟩).lower ∧ (cell12537 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12537 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12537 ⟨26,by decide⟩).lower ∧ (cell12537 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12537 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12537 ⟨27,by decide⟩).lower ∧ (cell12537 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12537 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12537 ⟨28,by decide⟩).lower ∧ (cell12537 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12537 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12537 ⟨29,by decide⟩).lower ∧ (cell12537 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12537 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12537 ⟨30,by decide⟩).lower ∧ (cell12537 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12537 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12537 ⟨31,by decide⟩).lower ∧ (cell12537 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12537 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12537 ⟨32,by decide⟩).lower ∧ (cell12537 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12537 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12537 ⟨33,by decide⟩).lower ∧ (cell12537 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12537 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12537 ⟨34,by decide⟩).lower ∧ (cell12537 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12537 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12537 ⟨35,by decide⟩).lower ∧ (cell12537 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12537 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12537 ⟨36,by decide⟩).lower ∧ (cell12537 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12537 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12537 ⟨37,by decide⟩).lower ∧ (cell12537 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12537 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12537 ⟨38,by decide⟩).lower ∧ (cell12537 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12537 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12537 ⟨39,by decide⟩).lower ∧ (cell12537 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12537 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12537 ⟨40,by decide⟩).lower ∧ (cell12537 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12537 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12537 ⟨41,by decide⟩).lower ∧ (cell12537 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12537 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12537 ⟨42,by decide⟩).lower ∧ (cell12537 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12537 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12537 ⟨43,by decide⟩).lower ∧ (cell12537 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12537 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12537 ⟨44,by decide⟩).lower ∧ (cell12537 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12537 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12537 ⟨45,by decide⟩).lower ∧ (cell12537 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12537 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12537 ⟨46,by decide⟩).lower ∧ (cell12537 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12537 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12537 ⟨47,by decide⟩).lower ∧ (cell12537 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12537 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12537 ⟨48,by decide⟩).lower ∧ (cell12537 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12537 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12537 ⟨49,by decide⟩).lower ∧ (cell12537 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12537 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12537 ⟨50,by decide⟩).lower ∧ (cell12537 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12537 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12537 ⟨51,by decide⟩).lower ∧ (cell12537 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12537 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12537 ⟨52,by decide⟩).lower ∧ (cell12537 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12537 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12537 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12537 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12537,cell12537,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12537 i).lower ∧
    (cell12537 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12537 i).upper ≤ (0.532 : ℝ) ∧
    (cell12537 i).centre ≤ (0.1 : ℝ) ∧ (cell12537 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12537 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12537 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12537

/-! The local source numeric instances at 12537 have no network premises. -/
namespace BstLean.Part269.N12537
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12537)
open BstLean.Part268 (cell12537)

noncomputable def sourceNumerics12537 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12537 (cell12537 i)
      scalarRow12537.M scalarRow12537.H scalarRow12537.xi := by
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
    energy_allowance := scalarRow12537.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12537]
    centre_nonneg := (scalarRow12537.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D7.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12537])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12537