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
import BstLean.Part269Direction28
import BstLean.Part269Shared28
import BstLean.Part269Finite
import BstLean.Part269Rows28
import BstLean.Part269Source
/-! Actual 13063 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13063 ≤ (1.035303829712 : ℝ) := by
  have hr : (114.293481878889 : ℝ) ≤ √(13063 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.293481878889 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13063 13063 (11 / 1000) ≤
    (0.008363442178 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13063) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.293481878889 : ℝ) ≤ √(13063 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13063)
  have hdiv : K / √(13063 : ℝ) ≤ K / 114.293481878889 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.293481878889 ≤ (0.008363442178 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13063.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13063 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13063 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13063 := gPlus_lower 13063
end BstLean.Part269.N13063

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13063
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035303829711 : ℝ) ≤ wn 13063 := by
  have hn : √(13063 : ℝ) ≤ 114.293481878890 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13063 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.293481878890 ≤ 2 / √(13063 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244762018 : ℝ) ≤ rhoBar 13063 BstLean.Part154.csC ∧
    rhoBar 13063 BstLean.Part154.csC ≤ 0.000244762397 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035303829711 : ℝ) / (1.295212 * 13063) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035303829712 : ℝ) / (1.29521 * 13063) := by gcongr
      _ ≤ (0.000244762397 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13063 BstLean.Part154.csC) ≤ 0.000979109497 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13063 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) ≤ 0.000186950924 ∧
    cc1 (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) ≤ 0.000118958165 ∧
    cc2 (rhoBar 13063 BstLean.Part154.csC) ≤ 0.000069056188 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13063 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13063 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13063 BstLean.Part154.csC * nuR (rhoBar 13063 BstLean.Part154.csC)) ≤ 0.000489539772 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244762397 : ℝ) * 0.000979109497 := by gcongr
      _ ≤ (0.000489539772 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13063 BstLean.Part154.csC) * nuR (rhoBar 13063 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979109497 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13063 BstLean.Part154.csC) * rhoBar 13063 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244762397 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244762397 / 2 + 0.399 * 0.000979109497 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186950924 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489539772 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118958165 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244762397 / 1.414213562 := by gcongr
      _ ≤ (0.000069056188 : ℝ) := by norm_num

end BstLean.Part269.N13063

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13063
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) ≤ 1.50935E-7 := by
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13063 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13063 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13063 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186950924 : ℝ) ^ 2 + 0.000118958165 ^ 2 + 3 * 0.000069056188 ^ 2 +
        2 * 0.797885 * 0.000186950924 * 0.000118958165 + 2 * 0.000186950924 * 0.000069056188 +
        4 * 0.797885 * 0.000118958165 * 0.000069056188 := by gcongr
    _ ≤ (1.50935E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13063 BstLean.Part154.csC Θ ≤ 0.002553722752 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13063 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13063 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13063 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035303829712 * 1.50935E-7 / (0.000244762018 : ℝ) := by gcongr
    _ ≤ 0.002553722752 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13063 BstLean.Part154.csC Θ ≤ 0.002832115208 + 0.000645286714 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13063 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13063 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035303829712 : ℝ) * ((2 * Θ * 0.000244762397 +
        (6863 / 10000) * 0.000244762397 * 13063 * 0.000979109497) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002832115208 + 0.000645286714 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13063 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13063 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13063 0.011 Θ ∧ gammaRatio 13063 0.011 Θ ≤ 0.000084142983 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13063 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035303829712 : ℝ) * 0.525 / ((1 - 0.011) * 13063) := by gcongr
      _ ≤ (0.000084142983 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13063 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13063 0.011 Θ) :=
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
    badAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13063 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13063 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13063 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13063 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13063 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13063 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13063 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13063 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13063 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13063 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035303829712 : ℝ) * 13063 *
        (1.3781E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003215864595 + 0.003199009466 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13063

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13063
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13063 BstLean.Part154.csC) (piBar (rhoBar 13063 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13063 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13063 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13063 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13063 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13063 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13063 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13063 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13063 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13063 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13063 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051742095692 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13063) ≤ 0.010448868662 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13063 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035303829712)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010448868662 + 2 * 0.737676 / 13063) := by gcongr
    _ ≤ (0.051742095692 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13063 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13063

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13063
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519528056 : ℝ) ≤ plow 13063 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13063) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401944565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340704445) : eMP 13063 0.011 xi bn ≤ 0.001154705178 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13063 : ℝ) * (1 - 0.011))) ≤ 0.000570981288 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340704445 / (13063 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570981288 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570981288 : ℝ) + 3.141593 * 0.052401944565 / (13063 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154705178 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401944565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340704445) : PiBarMP 13063 12 0.011 xi bn ≤ 0.158972604578 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13063 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036615631157 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.663129465979 : ℝ) ≤ √((13063 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.293481878889 : ℝ) ≤ √(13063 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13063) ≤ 0.121900287171 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036615631157 + 0.052401944565 * 1.772454 / (2 * (113.663129465979 : ℝ))) * (1 + 0.001154705178) +
        8 / (13063 * 114.293481878889) + 0.121900287171 := by gcongr
    _ ≤ (0.158972604578 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401944565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340704445) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280656805934) :
    parallelOracle 13063 0.011 xi bn cd ≤ 0.159935590881 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13063 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13063 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519528056 : ℝ) ≤ plow 13063 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.293481878889 : ℝ) ≤ √(13063 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280656805934 : ℝ) / (2 * 0.560519528056 * 114.293481878889)) * 0.158972604578 +
        0.280656805934 ^ 2 / (2 * 0.560519528056 * 114.293481878889) := by gcongr
    _ ≤ (0.159935590881 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401944565) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340704445)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280656805934) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13063 13063 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519528056 : ℝ) ≤ plow 13063 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.293481878889 : ℝ) ≤ √(13063 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13063 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13063 Θ 1.22 ≤ 0.011602590789 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.293481878889 := by gcongr <;> linarith
      _ ≤ (0.011602590789 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13063 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13063 13063 0.011 ≤ 0.008363442178 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13063 13063 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13063 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13063 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13063 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13063 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159935590881 + 0.011602590789 + (0.008363442178 : ℝ) *
        (1 + 2 * (0.280656805934 + 0.011602590789) / (0.560519528056 * 114.293481878889))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13063]

end BstLean.Part269.N13063

/-! The original eight local profiles supply actual 13063 moment certificates. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13063 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052401944565 ∧
    0 ≤ bN 13063 BstLean.Part154.csC (groupTheta g) ∧ bN 13063 BstLean.Part154.csC (groupTheta g) ≤ 0.001340704445 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13063 13063 0.011
      (momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13063 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13063 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13063 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228914710242 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13063 0.011
      (momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13063 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13063
/-! The actual computed-centre upper energy formula at 13063. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13063

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13063)
open BstLean.Part268 (cell13063)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084496714238
  | 2 => 0.085423265295
  | 3 => 0.086345707310
  | 4 => 0.087264929828
  | 5 => 0.088182024112
  | 6 => 0.089098314986
  | 7 => 0.090015396041
  | 8 => 0.090935168293
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13063 13063 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13063 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13063

/-! Actual upper energy certificates on all 43 source endpoints at 13063. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13063)
open BstLean.Part268 (cell13063)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13063 (gMinus 13063) (1 - (cell13063 i).lower) ≤ 1 ∧
    energyUpper 13063 (gMinus 13063) (BstLean.Part211.gPlus 13063)
      (finiteEnergy 13063 13063 0.011) (1 - (cell13063 i).lower) ≤
      (cell13063 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨10,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨11,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨12,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨13,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨14,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨15,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨16,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨17,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨18,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨19,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨20,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨21,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨22,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨23,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨24,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨25,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨26,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨27,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨28,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨29,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨30,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨31,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨32,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨33,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨34,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨35,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨36,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨37,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨38,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨39,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨40,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨41,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨42,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨43,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨44,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨45,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨46,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨47,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨48,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨49,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨50,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨51,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13063) (by norm_num)
        (q := 1 - (cell13063 ⟨52,by decide⟩).lower)
        (by norm_num [cell13063]) (by norm_num [cell13063])
      exact ⟨E.1,E.2.trans (by norm_num [cell13063])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13063

/-! Source-cell containment and simple scalar guards at 13063. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13063)
open BstLean.Part268 (cell13063)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13063 ⟨10,by decide⟩).lower ∧ (cell13063 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13063 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13063 ⟨11,by decide⟩).lower ∧ (cell13063 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13063 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13063 ⟨12,by decide⟩).lower ∧ (cell13063 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13063 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13063 ⟨13,by decide⟩).lower ∧ (cell13063 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13063 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13063 ⟨14,by decide⟩).lower ∧ (cell13063 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13063 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13063 ⟨15,by decide⟩).lower ∧ (cell13063 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13063 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13063 ⟨16,by decide⟩).lower ∧ (cell13063 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13063 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13063 ⟨17,by decide⟩).lower ∧ (cell13063 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13063 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13063 ⟨18,by decide⟩).lower ∧ (cell13063 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13063 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13063 ⟨19,by decide⟩).lower ∧ (cell13063 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13063 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13063 ⟨20,by decide⟩).lower ∧ (cell13063 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13063 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13063 ⟨21,by decide⟩).lower ∧ (cell13063 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13063 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13063 ⟨22,by decide⟩).lower ∧ (cell13063 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13063 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13063 ⟨23,by decide⟩).lower ∧ (cell13063 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13063 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13063 ⟨24,by decide⟩).lower ∧ (cell13063 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13063 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13063 ⟨25,by decide⟩).lower ∧ (cell13063 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13063 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13063 ⟨26,by decide⟩).lower ∧ (cell13063 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13063 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13063 ⟨27,by decide⟩).lower ∧ (cell13063 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13063 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13063 ⟨28,by decide⟩).lower ∧ (cell13063 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13063 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13063 ⟨29,by decide⟩).lower ∧ (cell13063 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13063 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13063 ⟨30,by decide⟩).lower ∧ (cell13063 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13063 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13063 ⟨31,by decide⟩).lower ∧ (cell13063 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13063 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13063 ⟨32,by decide⟩).lower ∧ (cell13063 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13063 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13063 ⟨33,by decide⟩).lower ∧ (cell13063 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13063 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13063 ⟨34,by decide⟩).lower ∧ (cell13063 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13063 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13063 ⟨35,by decide⟩).lower ∧ (cell13063 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13063 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13063 ⟨36,by decide⟩).lower ∧ (cell13063 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13063 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13063 ⟨37,by decide⟩).lower ∧ (cell13063 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13063 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13063 ⟨38,by decide⟩).lower ∧ (cell13063 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13063 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13063 ⟨39,by decide⟩).lower ∧ (cell13063 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13063 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13063 ⟨40,by decide⟩).lower ∧ (cell13063 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13063 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13063 ⟨41,by decide⟩).lower ∧ (cell13063 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13063 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13063 ⟨42,by decide⟩).lower ∧ (cell13063 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13063 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13063 ⟨43,by decide⟩).lower ∧ (cell13063 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13063 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13063 ⟨44,by decide⟩).lower ∧ (cell13063 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13063 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13063 ⟨45,by decide⟩).lower ∧ (cell13063 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13063 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13063 ⟨46,by decide⟩).lower ∧ (cell13063 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13063 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13063 ⟨47,by decide⟩).lower ∧ (cell13063 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13063 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13063 ⟨48,by decide⟩).lower ∧ (cell13063 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13063 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13063 ⟨49,by decide⟩).lower ∧ (cell13063 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13063 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13063 ⟨50,by decide⟩).lower ∧ (cell13063 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13063 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13063 ⟨51,by decide⟩).lower ∧ (cell13063 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13063 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13063 ⟨52,by decide⟩).lower ∧ (cell13063 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13063 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13063 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13063 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13063,cell13063,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13063 i).lower ∧
    (cell13063 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13063 i).upper ≤ (0.532 : ℝ) ∧
    (cell13063 i).centre ≤ (0.1 : ℝ) ∧ (cell13063 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13063 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13063 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13063

/-! The local source numeric instances at 13063 have no network premises. -/
namespace BstLean.Part269.N13063
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13063)
open BstLean.Part268 (cell13063)

noncomputable def sourceNumerics13063 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13063 (cell13063 i)
      scalarRow13063.M scalarRow13063.H scalarRow13063.xi := by
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
    energy_allowance := scalarRow13063.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13063]
    centre_nonneg := (scalarRow13063.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13063])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13063
/-! Actual 13064 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13064 ≤ (1.035302466779 : ℝ) := by
  have hr : (114.297856497836 : ℝ) ≤ √(13064 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.297856497836 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13064 13064 (11 / 1000) ≤
    (0.008363122074 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13064) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.297856497836 : ℝ) ≤ √(13064 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13064)
  have hdiv : K / √(13064 : ℝ) ≤ K / 114.297856497836 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.297856497836 ≤ (0.008363122074 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13064.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13064 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13064 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13064 := gPlus_lower 13064
end BstLean.Part269.N13064

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13064
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035302466778 : ℝ) ≤ wn 13064 := by
  have hn : √(13064 : ℝ) ≤ 114.297856497837 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13064 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.297856497837 ≤ 2 / √(13064 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244742960 : ℝ) ≤ rhoBar 13064 BstLean.Part154.csC ∧
    rhoBar 13064 BstLean.Part154.csC ≤ 0.000244743339 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035302466778 : ℝ) / (1.295212 * 13064) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035302466779 : ℝ) / (1.29521 * 13064) := by gcongr
      _ ≤ (0.000244743339 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13064 BstLean.Part154.csC) ≤ 0.000979033256 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13064 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) ≤ 0.000186936367 ∧
    cc1 (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) ≤ 0.000118948902 ∧
    cc2 (rhoBar 13064 BstLean.Part154.csC) ≤ 0.000069050811 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13064 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13064 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13064 BstLean.Part154.csC * nuR (rhoBar 13064 BstLean.Part154.csC)) ≤ 0.000489501653 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244743339 : ℝ) * 0.000979033256 := by gcongr
      _ ≤ (0.000489501653 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13064 BstLean.Part154.csC) * nuR (rhoBar 13064 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000979033256 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13064 BstLean.Part154.csC) * rhoBar 13064 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244743339 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244743339 / 2 + 0.399 * 0.000979033256 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186936367 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489501653 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118948902 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244743339 / 1.414213562 := by gcongr
      _ ≤ (0.000069050811 : ℝ) := by norm_num

end BstLean.Part269.N13064

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13064
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) ≤ 1.50912E-7 := by
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13064 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13064 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13064 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186936367 : ℝ) ^ 2 + 0.000118948902 ^ 2 + 3 * 0.000069050811 ^ 2 +
        2 * 0.797885 * 0.000186936367 * 0.000118948902 + 2 * 0.000186936367 * 0.000069050811 +
        4 * 0.797885 * 0.000118948902 * 0.000069050811 := by gcongr
    _ ≤ (1.50912E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13064 BstLean.Part154.csC Θ ≤ 0.002553529072 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13064 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13064 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13064 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035302466779 * 1.50912E-7 / (0.000244742960 : ℝ) := by gcongr
    _ ≤ 0.002553529072 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13064 BstLean.Part154.csC Θ ≤ 0.002831887219 + 0.000645235620 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13064 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13064 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035302466779 : ℝ) * ((2 * Θ * 0.000244743339 +
        (6863 / 10000) * 0.000244743339 * 13064 * 0.000979033256) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002831887219 + 0.000645235620 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13064 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13064 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13064 0.011 Θ ∧ gammaRatio 13064 0.011 Θ ≤ 0.000084136431 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13064 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035302466779 : ℝ) * 0.525 / ((1 - 0.011) * 13064) := by gcongr
      _ ≤ (0.000084136431 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13064 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13064 0.011 Θ) :=
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
    badAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13064 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13064 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13064 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13064 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13064 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13064 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13064 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13064 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13064 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13064 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035302466779 : ℝ) * 13064 *
        (1.3781E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003215636606 + 0.003198764692 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13064

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13064
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13064 BstLean.Part154.csC) (piBar (rhoBar 13064 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13064 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13064 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13064 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13064 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13064 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13064 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13064 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13064 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13064 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13064 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051740094149 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13064) ≤ 0.010448468744 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13064 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035302466779)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010448468744 + 2 * 0.737676 / 13064) := by gcongr
    _ ≤ (0.051740094149 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13064 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13064

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13064
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519570797 : ℝ) ≤ plow 13064 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13064) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401588070)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340602763) : eMP 13064 0.011 xi bn ≤ 0.001154617106 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13064 : ℝ) * (1 - 0.011))) ≤ 0.000570937783 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340602763 / (13064 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570937783 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570937783 : ℝ) + 3.141593 * 0.052401588070 / (13064 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154617106 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401588070)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340602763) : PiBarMP 13064 12 0.011 xi bn ≤ 0.158966526536 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13064 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036614242625 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.667479957989 : ℝ) ≤ √((13064 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.297856497836 : ℝ) ≤ √(13064 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13064) ≤ 0.121895621578 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036614242625 + 0.052401588070 * 1.772454 / (2 * (113.667479957989 : ℝ))) * (1 + 0.001154617106) +
        8 / (13064 * 114.297856497836) + 0.121895621578 := by gcongr
    _ ≤ (0.158966526536 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401588070)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340602763) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280654025726) :
    parallelOracle 13064 0.011 xi bn cd ≤ 0.159929446967 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13064 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13064 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519570797 : ℝ) ≤ plow 13064 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.297856497836 : ℝ) ≤ √(13064 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280654025726 : ℝ) / (2 * 0.560519570797 * 114.297856497836)) * 0.158966526536 +
        0.280654025726 ^ 2 / (2 * 0.560519570797 * 114.297856497836) := by gcongr
    _ ≤ (0.159929446967 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401588070) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340602763)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280654025726) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13064 13064 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519570797 : ℝ) ≤ plow 13064 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.297856497836 : ℝ) ≤ √(13064 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13064 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13064 Θ 1.22 ≤ 0.011602146713 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.297856497836 := by gcongr <;> linarith
      _ ≤ (0.011602146713 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13064 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13064 13064 0.011 ≤ 0.008363122074 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13064 13064 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13064 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13064 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13064 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13064 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159929446967 + 0.011602146713 + (0.008363122074 : ℝ) *
        (1 + 2 * (0.280654025726 + 0.011602146713) / (0.560519570797 * 114.297856497836))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13064]

end BstLean.Part269.N13064

/-! The original eight local profiles supply actual 13064 moment certificates. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13064 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052401588070 ∧
    0 ≤ bN 13064 BstLean.Part154.csC (groupTheta g) ∧ bN 13064 BstLean.Part154.csC (groupTheta g) ≤ 0.001340602763 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13064 13064 0.011
      (momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13064 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13064 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13064 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228913931577 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13064 0.011
      (momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13064 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13064
/-! The actual computed-centre upper energy formula at 13064. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13064

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13064)
open BstLean.Part268 (cell13064)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084494145438
  | 2 => 0.085420663674
  | 3 => 0.086343068027
  | 4 => 0.087262246898
  | 5 => 0.088179290197
  | 6 => 0.089095521155
  | 7 => 0.090012531500
  | 8 => 0.090932220085
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13064 13064 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13064 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13064

/-! Actual upper energy certificates on all 43 source endpoints at 13064. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13064)
open BstLean.Part268 (cell13064)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13064 (gMinus 13064) (1 - (cell13064 i).lower) ≤ 1 ∧
    energyUpper 13064 (gMinus 13064) (BstLean.Part211.gPlus 13064)
      (finiteEnergy 13064 13064 0.011) (1 - (cell13064 i).lower) ≤
      (cell13064 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨10,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨11,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨12,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨13,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨14,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨15,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨16,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨17,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨18,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨19,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨20,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨21,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨22,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨23,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨24,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨25,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨26,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨27,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨28,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨29,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨30,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨31,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨32,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨33,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨34,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨35,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨36,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨37,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨38,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨39,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨40,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨41,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨42,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨43,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨44,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨45,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨46,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨47,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨48,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨49,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨50,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨51,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13064) (by norm_num)
        (q := 1 - (cell13064 ⟨52,by decide⟩).lower)
        (by norm_num [cell13064]) (by norm_num [cell13064])
      exact ⟨E.1,E.2.trans (by norm_num [cell13064])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13064

/-! Source-cell containment and simple scalar guards at 13064. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13064)
open BstLean.Part268 (cell13064)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13064 ⟨10,by decide⟩).lower ∧ (cell13064 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13064 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13064 ⟨11,by decide⟩).lower ∧ (cell13064 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13064 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13064 ⟨12,by decide⟩).lower ∧ (cell13064 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13064 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13064 ⟨13,by decide⟩).lower ∧ (cell13064 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13064 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13064 ⟨14,by decide⟩).lower ∧ (cell13064 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13064 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13064 ⟨15,by decide⟩).lower ∧ (cell13064 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13064 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13064 ⟨16,by decide⟩).lower ∧ (cell13064 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13064 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13064 ⟨17,by decide⟩).lower ∧ (cell13064 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13064 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13064 ⟨18,by decide⟩).lower ∧ (cell13064 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13064 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13064 ⟨19,by decide⟩).lower ∧ (cell13064 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13064 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13064 ⟨20,by decide⟩).lower ∧ (cell13064 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13064 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13064 ⟨21,by decide⟩).lower ∧ (cell13064 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13064 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13064 ⟨22,by decide⟩).lower ∧ (cell13064 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13064 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13064 ⟨23,by decide⟩).lower ∧ (cell13064 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13064 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13064 ⟨24,by decide⟩).lower ∧ (cell13064 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13064 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13064 ⟨25,by decide⟩).lower ∧ (cell13064 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13064 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13064 ⟨26,by decide⟩).lower ∧ (cell13064 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13064 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13064 ⟨27,by decide⟩).lower ∧ (cell13064 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13064 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13064 ⟨28,by decide⟩).lower ∧ (cell13064 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13064 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13064 ⟨29,by decide⟩).lower ∧ (cell13064 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13064 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13064 ⟨30,by decide⟩).lower ∧ (cell13064 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13064 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13064 ⟨31,by decide⟩).lower ∧ (cell13064 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13064 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13064 ⟨32,by decide⟩).lower ∧ (cell13064 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13064 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13064 ⟨33,by decide⟩).lower ∧ (cell13064 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13064 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13064 ⟨34,by decide⟩).lower ∧ (cell13064 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13064 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13064 ⟨35,by decide⟩).lower ∧ (cell13064 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13064 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13064 ⟨36,by decide⟩).lower ∧ (cell13064 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13064 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13064 ⟨37,by decide⟩).lower ∧ (cell13064 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13064 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13064 ⟨38,by decide⟩).lower ∧ (cell13064 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13064 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13064 ⟨39,by decide⟩).lower ∧ (cell13064 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13064 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13064 ⟨40,by decide⟩).lower ∧ (cell13064 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13064 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13064 ⟨41,by decide⟩).lower ∧ (cell13064 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13064 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13064 ⟨42,by decide⟩).lower ∧ (cell13064 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13064 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13064 ⟨43,by decide⟩).lower ∧ (cell13064 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13064 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13064 ⟨44,by decide⟩).lower ∧ (cell13064 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13064 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13064 ⟨45,by decide⟩).lower ∧ (cell13064 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13064 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13064 ⟨46,by decide⟩).lower ∧ (cell13064 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13064 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13064 ⟨47,by decide⟩).lower ∧ (cell13064 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13064 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13064 ⟨48,by decide⟩).lower ∧ (cell13064 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13064 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13064 ⟨49,by decide⟩).lower ∧ (cell13064 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13064 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13064 ⟨50,by decide⟩).lower ∧ (cell13064 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13064 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13064 ⟨51,by decide⟩).lower ∧ (cell13064 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13064 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13064 ⟨52,by decide⟩).lower ∧ (cell13064 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13064 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13064 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13064 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13064,cell13064,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13064 i).lower ∧
    (cell13064 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13064 i).upper ≤ (0.532 : ℝ) ∧
    (cell13064 i).centre ≤ (0.1 : ℝ) ∧ (cell13064 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13064 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13064 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13064

/-! The local source numeric instances at 13064 have no network premises. -/
namespace BstLean.Part269.N13064
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13064)
open BstLean.Part268 (cell13064)

noncomputable def sourceNumerics13064 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13064 (cell13064 i)
      scalarRow13064.M scalarRow13064.H scalarRow13064.xi := by
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
    energy_allowance := scalarRow13064.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13064]
    centre_nonneg := (scalarRow13064.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13064])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13064
/-! Actual 13065 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13065 ≤ (1.035301104003 : ℝ) := by
  have hr : (114.302230949356 : ℝ) ≤ √(13065 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.302230949356 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13065 13065 (11 / 1000) ≤
    (0.008362802008 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13065) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.302230949356 : ℝ) ≤ √(13065 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13065)
  have hdiv : K / √(13065 : ℝ) ≤ K / 114.302230949356 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.302230949356 ≤ (0.008362802008 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13065.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13065 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13065 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13065 := gPlus_lower 13065
end BstLean.Part269.N13065

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13065
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035301104002 : ℝ) ≤ wn 13065 := by
  have hn : √(13065 : ℝ) ≤ 114.302230949357 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13065 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.302230949357 ≤ 2 / √(13065 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244723905 : ℝ) ≤ rhoBar 13065 BstLean.Part154.csC ∧
    rhoBar 13065 BstLean.Part154.csC ≤ 0.000244724284 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035301104002 : ℝ) / (1.295212 * 13065) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035301104003 : ℝ) / (1.29521 * 13065) := by gcongr
      _ ≤ (0.000244724284 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13065 BstLean.Part154.csC) ≤ 0.000978957026 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13065 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) ≤ 0.000186921812 ∧
    cc1 (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) ≤ 0.000118939641 ∧
    cc2 (rhoBar 13065 BstLean.Part154.csC) ≤ 0.000069045435 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13065 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13065 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13065 BstLean.Part154.csC * nuR (rhoBar 13065 BstLean.Part154.csC)) ≤ 0.000489463541 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244724284 : ℝ) * 0.000978957026 := by gcongr
      _ ≤ (0.000489463541 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13065 BstLean.Part154.csC) * nuR (rhoBar 13065 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978957026 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13065 BstLean.Part154.csC) * rhoBar 13065 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244724284 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244724284 / 2 + 0.399 * 0.000978957026 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186921812 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489463541 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118939641 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244724284 / 1.414213562 := by gcongr
      _ ≤ (0.000069045435 : ℝ) := by norm_num

end BstLean.Part269.N13065

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13065
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) ≤ 1.50888E-7 := by
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13065 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13065 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13065 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186921812 : ℝ) ^ 2 + 0.000118939641 ^ 2 + 3 * 0.000069045435 ^ 2 +
        2 * 0.797885 * 0.000186921812 * 0.000118939641 + 2 * 0.000186921812 * 0.000069045435 +
        4 * 0.797885 * 0.000118939641 * 0.000069045435 := by gcongr
    _ ≤ (1.50888E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13065 BstLean.Part154.csC Θ ≤ 0.002553318410 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13065 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13065 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13065 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035301104003 * 1.50888E-7 / (0.000244723905 : ℝ) := by gcongr
    _ ≤ 0.002553318410 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13065 BstLean.Part154.csC Θ ≤ 0.002831659266 + 0.000645184535 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13065 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13065 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035301104003 : ℝ) * ((2 * Θ * 0.000244724284 +
        (6863 / 10000) * 0.000244724284 * 13065 * 0.000978957026) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002831659266 + 0.000645184535 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13065 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13065 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13065 0.011 Θ ∧ gammaRatio 13065 0.011 Θ ≤ 0.000084129881 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13065 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035301104003 : ℝ) * 0.525 / ((1 - 0.011) * 13065) := by gcongr
      _ ≤ (0.000084129881 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13065 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13065 0.011 Θ) :=
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
    badAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13065 BstLean.Part154.csC) 1.22 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 2 (rhoBar 13065 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13065 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13065 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13065 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13065 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13065 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13065 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13065 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13065 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035301104003 : ℝ) * 13065 *
        (1.3781E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003215408653 + 0.003198502945 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13065

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13065
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13065 BstLean.Part154.csC) (piBar (rhoBar 13065 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13065 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13065 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13065 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13065 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13065 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13065 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13065 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13065 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13065 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13065 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051738092833 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13065) ≤ 0.010448068871 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13065 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035301104003)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010448068871 + 2 * 0.737676 / 13065) := by gcongr
    _ ≤ (0.051738092833 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13065 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13065

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13065
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519613532 : ℝ) ≤ plow 13065 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13065) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401222700)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340492166) : eMP 13065 0.011 xi bn ≤ 0.001154525240 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13065 : ℝ) * (1 - 0.011))) ≤ 0.000570892382 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340492166 / (13065 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570892382 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570892382 : ℝ) + 3.141593 * 0.052401222700 / (13065 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154525240 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401222700)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340492166) : PiBarMP 13065 12 0.011 xi bn ≤ 0.158960326881 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13065 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036612732294 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.671830283496 : ℝ) ≤ √((13065 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.302230949356 : ℝ) ≤ √(13065 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13065) ≤ 0.121890956520 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036612732294 + 0.052401222700 * 1.772454 / (2 * (113.671830283496 : ℝ))) * (1 + 0.001154525240) +
        8 / (13065 * 114.302230949356) + 0.121890956520 := by gcongr
    _ ≤ (0.158960326881 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401222700)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340492166) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280651226358) :
    parallelOracle 13065 0.011 xi bn cd ≤ 0.159923181073 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13065 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13065 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519613532 : ℝ) ≤ plow 13065 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.302230949356 : ℝ) ≤ √(13065 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280651226358 : ℝ) / (2 * 0.560519613532 * 114.302230949356)) * 0.158960326881 +
        0.280651226358 ^ 2 / (2 * 0.560519613532 * 114.302230949356) := by gcongr
    _ ≤ (0.159923181073 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052401222700) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340492166)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280651226358) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13065 13065 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519613532 : ℝ) ≤ plow 13065 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.302230949356 : ℝ) ≤ √(13065 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13065 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13065 Θ 1.22 ≤ 0.011601702688 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.302230949356 := by gcongr <;> linarith
      _ ≤ (0.011601702688 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13065 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13065 13065 0.011 ≤ 0.008362802008 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13065 13065 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13065 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13065 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13065 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13065 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159923181073 + 0.011601702688 + (0.008362802008 : ℝ) *
        (1 + 2 * (0.280651226358 + 0.011601702688) / (0.560519613532 * 114.302230949356))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13065]

end BstLean.Part269.N13065

/-! The original eight local profiles supply actual 13065 moment certificates. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13065 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052401222700 ∧
    0 ≤ bN 13065 BstLean.Part154.csC (groupTheta g) ∧ bN 13065 BstLean.Part154.csC (groupTheta g) ≤ 0.001340492166 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13065 13065 0.011
      (momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13065 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13065 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13065 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228913133525 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13065 0.011
      (momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13065 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13065
/-! The actual computed-centre upper energy formula at 13065. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13065

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13065)
open BstLean.Part268 (cell13065)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084491577401
  | 2 => 0.085418062840
  | 3 => 0.086340429564
  | 4 => 0.087259564829
  | 5 => 0.088176557192
  | 6 => 0.089092728294
  | 7 => 0.090009668002
  | 8 => 0.090929273011
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13065 13065 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13065 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13065

/-! Actual upper energy certificates on all 43 source endpoints at 13065. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13065)
open BstLean.Part268 (cell13065)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13065 (gMinus 13065) (1 - (cell13065 i).lower) ≤ 1 ∧
    energyUpper 13065 (gMinus 13065) (BstLean.Part211.gPlus 13065)
      (finiteEnergy 13065 13065 0.011) (1 - (cell13065 i).lower) ≤
      (cell13065 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨10,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨11,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨12,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨13,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨14,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨15,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨16,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨17,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨18,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨19,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨20,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨21,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨22,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨23,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨24,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨25,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨26,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨27,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨28,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨29,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨30,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨31,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨32,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨33,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨34,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨35,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨36,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨37,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨38,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨39,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨40,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨41,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨42,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨43,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨44,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨45,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨46,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨47,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨48,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨49,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨50,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨51,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13065) (by norm_num)
        (q := 1 - (cell13065 ⟨52,by decide⟩).lower)
        (by norm_num [cell13065]) (by norm_num [cell13065])
      exact ⟨E.1,E.2.trans (by norm_num [cell13065])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13065

/-! Source-cell containment and simple scalar guards at 13065. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13065)
open BstLean.Part268 (cell13065)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13065 ⟨10,by decide⟩).lower ∧ (cell13065 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13065 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13065 ⟨11,by decide⟩).lower ∧ (cell13065 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13065 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13065 ⟨12,by decide⟩).lower ∧ (cell13065 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13065 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13065 ⟨13,by decide⟩).lower ∧ (cell13065 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13065 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13065 ⟨14,by decide⟩).lower ∧ (cell13065 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13065 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13065 ⟨15,by decide⟩).lower ∧ (cell13065 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13065 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13065 ⟨16,by decide⟩).lower ∧ (cell13065 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13065 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13065 ⟨17,by decide⟩).lower ∧ (cell13065 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13065 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13065 ⟨18,by decide⟩).lower ∧ (cell13065 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13065 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13065 ⟨19,by decide⟩).lower ∧ (cell13065 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13065 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13065 ⟨20,by decide⟩).lower ∧ (cell13065 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13065 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13065 ⟨21,by decide⟩).lower ∧ (cell13065 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13065 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13065 ⟨22,by decide⟩).lower ∧ (cell13065 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13065 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13065 ⟨23,by decide⟩).lower ∧ (cell13065 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13065 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13065 ⟨24,by decide⟩).lower ∧ (cell13065 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13065 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13065 ⟨25,by decide⟩).lower ∧ (cell13065 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13065 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13065 ⟨26,by decide⟩).lower ∧ (cell13065 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13065 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13065 ⟨27,by decide⟩).lower ∧ (cell13065 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13065 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13065 ⟨28,by decide⟩).lower ∧ (cell13065 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13065 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13065 ⟨29,by decide⟩).lower ∧ (cell13065 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13065 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13065 ⟨30,by decide⟩).lower ∧ (cell13065 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13065 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13065 ⟨31,by decide⟩).lower ∧ (cell13065 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13065 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13065 ⟨32,by decide⟩).lower ∧ (cell13065 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13065 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13065 ⟨33,by decide⟩).lower ∧ (cell13065 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13065 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13065 ⟨34,by decide⟩).lower ∧ (cell13065 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13065 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13065 ⟨35,by decide⟩).lower ∧ (cell13065 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13065 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13065 ⟨36,by decide⟩).lower ∧ (cell13065 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13065 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13065 ⟨37,by decide⟩).lower ∧ (cell13065 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13065 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13065 ⟨38,by decide⟩).lower ∧ (cell13065 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13065 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13065 ⟨39,by decide⟩).lower ∧ (cell13065 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13065 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13065 ⟨40,by decide⟩).lower ∧ (cell13065 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13065 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13065 ⟨41,by decide⟩).lower ∧ (cell13065 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13065 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13065 ⟨42,by decide⟩).lower ∧ (cell13065 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13065 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13065 ⟨43,by decide⟩).lower ∧ (cell13065 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13065 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13065 ⟨44,by decide⟩).lower ∧ (cell13065 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13065 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13065 ⟨45,by decide⟩).lower ∧ (cell13065 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13065 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13065 ⟨46,by decide⟩).lower ∧ (cell13065 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13065 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13065 ⟨47,by decide⟩).lower ∧ (cell13065 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13065 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13065 ⟨48,by decide⟩).lower ∧ (cell13065 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13065 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13065 ⟨49,by decide⟩).lower ∧ (cell13065 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13065 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13065 ⟨50,by decide⟩).lower ∧ (cell13065 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13065 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13065 ⟨51,by decide⟩).lower ∧ (cell13065 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13065 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13065 ⟨52,by decide⟩).lower ∧ (cell13065 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13065 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13065 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13065 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13065,cell13065,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13065 i).lower ∧
    (cell13065 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13065 i).upper ≤ (0.532 : ℝ) ∧
    (cell13065 i).centre ≤ (0.1 : ℝ) ∧ (cell13065 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13065 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13065 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13065

/-! The local source numeric instances at 13065 have no network premises. -/
namespace BstLean.Part269.N13065
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13065)
open BstLean.Part268 (cell13065)

noncomputable def sourceNumerics13065 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13065 (cell13065 i)
      scalarRow13065.M scalarRow13065.H scalarRow13065.xi := by
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
    energy_allowance := scalarRow13065.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13065]
    centre_nonneg := (scalarRow13065.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13065])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13065
/-! Actual 13066 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13066 ≤ (1.035299741385 : ℝ) := by
  have hr : (114.306605233468 : ℝ) ≤ √(13066 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.306605233468 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13066 13066 (11 / 1000) ≤
    (0.008362481978 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13066) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.306605233468 : ℝ) ≤ √(13066 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13066)
  have hdiv : K / √(13066 : ℝ) ≤ K / 114.306605233468 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.306605233468 ≤ (0.008362481978 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13066.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13066 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13066 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13066 := gPlus_lower 13066
end BstLean.Part269.N13066

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13066
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035299741384 : ℝ) ≤ wn 13066 := by
  have hn : √(13066 : ℝ) ≤ 114.306605233469 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13066 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.306605233469 ≤ 2 / √(13066 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244704853 : ℝ) ≤ rhoBar 13066 BstLean.Part154.csC ∧
    rhoBar 13066 BstLean.Part154.csC ≤ 0.000244705232 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035299741384 : ℝ) / (1.295212 * 13066) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035299741385 : ℝ) / (1.29521 * 13066) := by gcongr
      _ ≤ (0.000244705232 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13066 BstLean.Part154.csC) ≤ 0.000978880809 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13066 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) ≤ 0.000186907259 ∧
    cc1 (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) ≤ 0.000118930381 ∧
    cc2 (rhoBar 13066 BstLean.Part154.csC) ≤ 0.000069040059 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13066 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13066 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13066 BstLean.Part154.csC * nuR (rhoBar 13066 BstLean.Part154.csC)) ≤ 0.000489425435 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244705232 : ℝ) * 0.000978880809 := by gcongr
      _ ≤ (0.000489425435 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13066 BstLean.Part154.csC) * nuR (rhoBar 13066 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978880809 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13066 BstLean.Part154.csC) * rhoBar 13066 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244705232 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244705232 / 2 + 0.399 * 0.000978880809 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186907259 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489425435 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118930381 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244705232 / 1.414213562 := by gcongr
      _ ≤ (0.000069040059 : ℝ) := by norm_num

end BstLean.Part269.N13066

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13066
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) ≤ 1.50865E-7 := by
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13066 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13066 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13066 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186907259 : ℝ) ^ 2 + 0.000118930381 ^ 2 + 3 * 0.000069040059 ^ 2 +
        2 * 0.797885 * 0.000186907259 * 0.000118930381 + 2 * 0.000186907259 * 0.000069040059 +
        4 * 0.797885 * 0.000118930381 * 0.000069040059 := by gcongr
    _ ≤ (1.50865E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13066 BstLean.Part154.csC Θ ≤ 0.002553124609 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13066 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13066 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13066 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035299741385 * 1.50865E-7 / (0.000244704853 : ℝ) := by gcongr
    _ ≤ 0.002553124609 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13066 BstLean.Part154.csC Θ ≤ 0.002831431352 + 0.000645133457 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13066 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13066 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035299741385 : ℝ) * ((2 * Θ * 0.000244705232 +
        (6863 / 10000) * 0.000244705232 * 13066 * 0.000978880809) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002831431352 + 0.000645133457 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13066 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13066 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13066 0.011 Θ ∧ gammaRatio 13066 0.011 Θ ≤ 0.000084123331 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13066 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035299741385 : ℝ) * 0.525 / ((1 - 0.011) * 13066) := by gcongr
      _ ≤ (0.000084123331 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13066 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13066 0.011 Θ) :=
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
    badAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13066 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13066 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13066 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13066 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13066 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13066 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13066 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13066 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13066 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13066 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035299741385 : ℝ) * 13066 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003215180739 + 0.003198258066 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13066

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13066
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13066 BstLean.Part154.csC) (piBar (rhoBar 13066 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13066 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13066 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13066 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13066 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13066 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13066 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13066 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13066 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13066 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13066 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051736091754 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13066) ≤ 0.010447669045 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13066 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035299741385)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010447669045 + 2 * 0.737676 / 13066) := by gcongr
    _ ≤ (0.051736091754 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13066 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13066

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13066
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519656260 : ℝ) ≤ plow 13066 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13066) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400866224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340390420) : eMP 13066 0.011 xi bn ≤ 0.001154437154 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13066 : ℝ) * (1 - 0.011))) ≤ 0.000570848870 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340390420 / (13066 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570848870 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570848870 : ℝ) + 3.141593 * 0.052400866224 / (13066 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154437154 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400866224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340390420) : PiBarMP 13066 12 0.011 xi bn ≤ 0.158954248928 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13066 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036611342778 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.676180442518 : ℝ) ≤ √((13066 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.306605233468 : ℝ) ≤ √(13066 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13066) ≤ 0.121886291998 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036611342778 + 0.052400866224 * 1.772454 / (2 * (113.676180442518 : ℝ))) * (1 + 0.001154437154) +
        8 / (13066 * 114.306605233468) + 0.121886291998 := by gcongr
    _ ≤ (0.158954248928 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400866224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340390420) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280648446650) :
    parallelOracle 13066 0.011 xi bn cd ≤ 0.159917037264 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13066 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13066 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519656260 : ℝ) ≤ plow 13066 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.306605233468 : ℝ) ≤ √(13066 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280648446650 : ℝ) / (2 * 0.560519656260 * 114.306605233468)) * 0.158954248928 +
        0.280648446650 ^ 2 / (2 * 0.560519656260 * 114.306605233468) := by gcongr
    _ ≤ (0.159917037264 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400866224) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340390420)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280648446650) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13066 13066 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519656260 : ℝ) ≤ plow 13066 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.306605233468 : ℝ) ≤ √(13066 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13066 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13066 Θ 1.22 ≤ 0.011601258714 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.306605233468 := by gcongr <;> linarith
      _ ≤ (0.011601258714 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13066 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13066 13066 0.011 ≤ 0.008362481978 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13066 13066 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13066 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13066 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13066 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13066 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159917037264 + 0.011601258714 + (0.008362481978 : ℝ) *
        (1 + 2 * (0.280648446650 + 0.011601258714) / (0.560519656260 * 114.306605233468))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13066]

end BstLean.Part269.N13066

/-! The original eight local profiles supply actual 13066 moment certificates. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13066 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052400866224 ∧
    0 ≤ bN 13066 BstLean.Part154.csC (groupTheta g) ∧ bN 13066 BstLean.Part154.csC (groupTheta g) ≤ 0.001340390420 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13066 13066 0.011
      (momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13066 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13066 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13066 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228912354896 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13066 0.011
      (momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13066 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13066
/-! The actual computed-centre upper energy formula at 13066. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13066

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13066)
open BstLean.Part268 (cell13066)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084489010124
  | 2 => 0.085415462794
  | 3 => 0.086337791920
  | 4 => 0.087256883620
  | 5 => 0.088173825097
  | 6 => 0.089089936404
  | 7 => 0.090006805548
  | 8 => 0.090926327068
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13066 13066 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13066 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13066

/-! Actual upper energy certificates on all 43 source endpoints at 13066. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13066)
open BstLean.Part268 (cell13066)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13066 (gMinus 13066) (1 - (cell13066 i).lower) ≤ 1 ∧
    energyUpper 13066 (gMinus 13066) (BstLean.Part211.gPlus 13066)
      (finiteEnergy 13066 13066 0.011) (1 - (cell13066 i).lower) ≤
      (cell13066 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨10,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨11,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨12,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨13,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨14,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨15,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨16,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨17,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨18,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨19,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨20,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨21,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨22,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨23,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨24,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨25,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨26,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨27,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨28,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨29,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨30,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨31,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨32,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨33,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨34,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨35,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨36,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨37,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨38,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨39,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨40,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨41,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨42,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨43,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨44,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨45,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨46,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨47,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨48,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨49,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨50,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨51,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13066) (by norm_num)
        (q := 1 - (cell13066 ⟨52,by decide⟩).lower)
        (by norm_num [cell13066]) (by norm_num [cell13066])
      exact ⟨E.1,E.2.trans (by norm_num [cell13066])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13066

/-! Source-cell containment and simple scalar guards at 13066. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13066)
open BstLean.Part268 (cell13066)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13066 ⟨10,by decide⟩).lower ∧ (cell13066 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13066 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13066 ⟨11,by decide⟩).lower ∧ (cell13066 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13066 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13066 ⟨12,by decide⟩).lower ∧ (cell13066 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13066 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13066 ⟨13,by decide⟩).lower ∧ (cell13066 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13066 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13066 ⟨14,by decide⟩).lower ∧ (cell13066 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13066 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13066 ⟨15,by decide⟩).lower ∧ (cell13066 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13066 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13066 ⟨16,by decide⟩).lower ∧ (cell13066 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13066 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13066 ⟨17,by decide⟩).lower ∧ (cell13066 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13066 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13066 ⟨18,by decide⟩).lower ∧ (cell13066 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13066 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13066 ⟨19,by decide⟩).lower ∧ (cell13066 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13066 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13066 ⟨20,by decide⟩).lower ∧ (cell13066 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13066 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13066 ⟨21,by decide⟩).lower ∧ (cell13066 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13066 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13066 ⟨22,by decide⟩).lower ∧ (cell13066 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13066 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13066 ⟨23,by decide⟩).lower ∧ (cell13066 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13066 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13066 ⟨24,by decide⟩).lower ∧ (cell13066 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13066 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13066 ⟨25,by decide⟩).lower ∧ (cell13066 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13066 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13066 ⟨26,by decide⟩).lower ∧ (cell13066 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13066 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13066 ⟨27,by decide⟩).lower ∧ (cell13066 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13066 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13066 ⟨28,by decide⟩).lower ∧ (cell13066 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13066 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13066 ⟨29,by decide⟩).lower ∧ (cell13066 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13066 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13066 ⟨30,by decide⟩).lower ∧ (cell13066 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13066 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13066 ⟨31,by decide⟩).lower ∧ (cell13066 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13066 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13066 ⟨32,by decide⟩).lower ∧ (cell13066 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13066 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13066 ⟨33,by decide⟩).lower ∧ (cell13066 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13066 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13066 ⟨34,by decide⟩).lower ∧ (cell13066 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13066 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13066 ⟨35,by decide⟩).lower ∧ (cell13066 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13066 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13066 ⟨36,by decide⟩).lower ∧ (cell13066 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13066 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13066 ⟨37,by decide⟩).lower ∧ (cell13066 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13066 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13066 ⟨38,by decide⟩).lower ∧ (cell13066 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13066 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13066 ⟨39,by decide⟩).lower ∧ (cell13066 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13066 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13066 ⟨40,by decide⟩).lower ∧ (cell13066 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13066 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13066 ⟨41,by decide⟩).lower ∧ (cell13066 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13066 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13066 ⟨42,by decide⟩).lower ∧ (cell13066 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13066 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13066 ⟨43,by decide⟩).lower ∧ (cell13066 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13066 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13066 ⟨44,by decide⟩).lower ∧ (cell13066 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13066 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13066 ⟨45,by decide⟩).lower ∧ (cell13066 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13066 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13066 ⟨46,by decide⟩).lower ∧ (cell13066 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13066 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13066 ⟨47,by decide⟩).lower ∧ (cell13066 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13066 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13066 ⟨48,by decide⟩).lower ∧ (cell13066 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13066 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13066 ⟨49,by decide⟩).lower ∧ (cell13066 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13066 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13066 ⟨50,by decide⟩).lower ∧ (cell13066 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13066 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13066 ⟨51,by decide⟩).lower ∧ (cell13066 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13066 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13066 ⟨52,by decide⟩).lower ∧ (cell13066 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13066 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13066 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13066 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13066,cell13066,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13066 i).lower ∧
    (cell13066 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13066 i).upper ≤ (0.532 : ℝ) ∧
    (cell13066 i).centre ≤ (0.1 : ℝ) ∧ (cell13066 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13066 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13066 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13066

/-! The local source numeric instances at 13066 have no network premises. -/
namespace BstLean.Part269.N13066
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13066)
open BstLean.Part268 (cell13066)

noncomputable def sourceNumerics13066 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13066 (cell13066 i)
      scalarRow13066.M scalarRow13066.H scalarRow13066.xi := by
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
    energy_allowance := scalarRow13066.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13066]
    centre_nonneg := (scalarRow13066.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13066])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13066
/-! Actual 13067 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13067 ≤ (1.035298378925 : ℝ) := by
  have hr : (114.310979350191 : ℝ) ≤ √(13067 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.310979350191 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13067 13067 (11 / 1000) ≤
    (0.008362161984 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13067) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.310979350191 : ℝ) ≤ √(13067 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13067)
  have hdiv : K / √(13067 : ℝ) ≤ K / 114.310979350191 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.310979350191 ≤ (0.008362161984 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13067.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13067 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13067 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13067 := gPlus_lower 13067
end BstLean.Part269.N13067

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13067
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035298378924 : ℝ) ≤ wn 13067 := by
  have hn : √(13067 : ℝ) ≤ 114.310979350192 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13067 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.310979350192 ≤ 2 / √(13067 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244685804 : ℝ) ≤ rhoBar 13067 BstLean.Part154.csC ∧
    rhoBar 13067 BstLean.Part154.csC ≤ 0.000244686183 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035298378924 : ℝ) / (1.295212 * 13067) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035298378925 : ℝ) / (1.29521 * 13067) := by gcongr
      _ ≤ (0.000244686183 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13067 BstLean.Part154.csC) ≤ 0.000978804604 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13067 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) ≤ 0.000186892709 ∧
    cc1 (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) ≤ 0.000118921123 ∧
    cc2 (rhoBar 13067 BstLean.Part154.csC) ≤ 0.000069034685 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13067 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13067 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13067 BstLean.Part154.csC * nuR (rhoBar 13067 BstLean.Part154.csC)) ≤ 0.000489387334 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244686183 : ℝ) * 0.000978804604 := by gcongr
      _ ≤ (0.000489387334 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13067 BstLean.Part154.csC) * nuR (rhoBar 13067 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978804604 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13067 BstLean.Part154.csC) * rhoBar 13067 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244686183 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244686183 / 2 + 0.399 * 0.000978804604 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186892709 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489387334 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118921123 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244686183 / 1.414213562 := by gcongr
      _ ≤ (0.000069034685 : ℝ) := by norm_num

end BstLean.Part269.N13067

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13067
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) ≤ 1.50841E-7 := by
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13067 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13067 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13067 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186892709 : ℝ) ^ 2 + 0.000118921123 ^ 2 + 3 * 0.000069034685 ^ 2 +
        2 * 0.797885 * 0.000186892709 * 0.000118921123 + 2 * 0.000186892709 * 0.000069034685 +
        4 * 0.797885 * 0.000118921123 * 0.000069034685 := by gcongr
    _ ≤ (1.50841E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13067 BstLean.Part154.csC Θ ≤ 0.002552913823 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13067 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13067 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13067 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035298378925 * 1.50841E-7 / (0.000244685804 : ℝ) := by gcongr
    _ ≤ 0.002552913823 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13067 BstLean.Part154.csC Θ ≤ 0.002831203475 + 0.000645082388 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13067 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13067 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035298378925 : ℝ) * ((2 * Θ * 0.000244686183 +
        (6863 / 10000) * 0.000244686183 * 13067 * 0.000978804604) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002831203475 + 0.000645082388 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13067 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13067 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13067 0.011 Θ ∧ gammaRatio 13067 0.011 Θ ≤ 0.000084116783 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13067 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035298378925 : ℝ) * 0.525 / ((1 - 0.011) * 13067) := by gcongr
      _ ≤ (0.000084116783 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13067 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13067 0.011 Θ) :=
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
    badAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13067 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13067 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13067 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13067 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13067 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13067 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13067 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13067 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13067 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13067 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035298378925 : ℝ) * 13067 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003214952862 + 0.003197996211 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13067

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13067
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13067 BstLean.Part154.csC) (piBar (rhoBar 13067 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13067 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13067 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13067 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13067 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13067 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13067 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13067 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13067 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13067 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13067 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051734090901 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13067) ≤ 0.010447269264 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13067 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035298378925)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010447269264 + 2 * 0.737676 / 13067) := by gcongr
    _ ≤ (0.051734090901 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13067 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13067

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13067
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519698982 : ℝ) ≤ plow 13067 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13067) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400500873)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340279758) : eMP 13067 0.011 xi bn ≤ 0.001154345274 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13067 : ℝ) * (1 - 0.011))) ≤ 0.000570803462 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340279758 / (13067 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570803462 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570803462 : ℝ) + 3.141593 * 0.052400500873 / (13067 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154345274 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400500873)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340279758) : PiBarMP 13067 12 0.011 xi bn ≤ 0.158948049342 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13067 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036609831440 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.680530435074 : ℝ) ≤ √((13067 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.310979350191 : ℝ) ≤ √(13067 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13067) ≤ 0.121881628012 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036609831440 + 0.052400500873 * 1.772454 / (2 * (113.680530435074 : ℝ))) * (1 + 0.001154345274) +
        8 / (13067 * 114.310979350191) + 0.121881628012 := by gcongr
    _ ≤ (0.158948049342 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400500873)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340279758) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280645647781) :
    parallelOracle 13067 0.011 xi bn cd ≤ 0.159910771455 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13067 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13067 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519698982 : ℝ) ≤ plow 13067 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.310979350191 : ℝ) ≤ √(13067 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280645647781 : ℝ) / (2 * 0.560519698982 * 114.310979350191)) * 0.158948049342 +
        0.280645647781 ^ 2 / (2 * 0.560519698982 * 114.310979350191) := by gcongr
    _ ≤ (0.159910771455 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400500873) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340279758)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280645647781) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13067 13067 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519698982 : ℝ) ≤ plow 13067 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.310979350191 : ℝ) ≤ √(13067 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13067 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13067 Θ 1.22 ≤ 0.011600814791 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.310979350191 := by gcongr <;> linarith
      _ ≤ (0.011600814791 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13067 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13067 13067 0.011 ≤ 0.008362161984 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13067 13067 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13067 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13067 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13067 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13067 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159910771455 + 0.011600814791 + (0.008362161984 : ℝ) *
        (1 + 2 * (0.280645647781 + 0.011600814791) / (0.560519698982 * 114.310979350191))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13067]

end BstLean.Part269.N13067

/-! The original eight local profiles supply actual 13067 moment certificates. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13067 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052400500873 ∧
    0 ≤ bN 13067 BstLean.Part154.csC (groupTheta g) ∧ bN 13067 BstLean.Part154.csC (groupTheta g) ≤ 0.001340279758 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13067 13067 0.011
      (momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13067 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13067 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13067 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228911556880 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13067 0.011
      (momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13067 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13067
/-! The actual computed-centre upper energy formula at 13067. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13067

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13067)
open BstLean.Part268 (cell13067)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084486443608
  | 2 => 0.085412863534
  | 3 => 0.086335155096
  | 4 => 0.087254203270
  | 5 => 0.088171093911
  | 6 => 0.089087145482
  | 7 => 0.090003944136
  | 8 => 0.090923382256
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13067 13067 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13067 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13067

/-! Actual upper energy certificates on all 43 source endpoints at 13067. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13067)
open BstLean.Part268 (cell13067)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13067 (gMinus 13067) (1 - (cell13067 i).lower) ≤ 1 ∧
    energyUpper 13067 (gMinus 13067) (BstLean.Part211.gPlus 13067)
      (finiteEnergy 13067 13067 0.011) (1 - (cell13067 i).lower) ≤
      (cell13067 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨10,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨11,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨12,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨13,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨14,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨15,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨16,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨17,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨18,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨19,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨20,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨21,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨22,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨23,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨24,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨25,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨26,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨27,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨28,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨29,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨30,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨31,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨32,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨33,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨34,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨35,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨36,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨37,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨38,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨39,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨40,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨41,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨42,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨43,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨44,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨45,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨46,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨47,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨48,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨49,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨50,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨51,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13067) (by norm_num)
        (q := 1 - (cell13067 ⟨52,by decide⟩).lower)
        (by norm_num [cell13067]) (by norm_num [cell13067])
      exact ⟨E.1,E.2.trans (by norm_num [cell13067])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13067

/-! Source-cell containment and simple scalar guards at 13067. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13067)
open BstLean.Part268 (cell13067)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13067 ⟨10,by decide⟩).lower ∧ (cell13067 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13067 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13067 ⟨11,by decide⟩).lower ∧ (cell13067 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13067 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13067 ⟨12,by decide⟩).lower ∧ (cell13067 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13067 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13067 ⟨13,by decide⟩).lower ∧ (cell13067 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13067 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13067 ⟨14,by decide⟩).lower ∧ (cell13067 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13067 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13067 ⟨15,by decide⟩).lower ∧ (cell13067 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13067 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13067 ⟨16,by decide⟩).lower ∧ (cell13067 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13067 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13067 ⟨17,by decide⟩).lower ∧ (cell13067 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13067 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13067 ⟨18,by decide⟩).lower ∧ (cell13067 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13067 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13067 ⟨19,by decide⟩).lower ∧ (cell13067 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13067 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13067 ⟨20,by decide⟩).lower ∧ (cell13067 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13067 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13067 ⟨21,by decide⟩).lower ∧ (cell13067 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13067 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13067 ⟨22,by decide⟩).lower ∧ (cell13067 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13067 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13067 ⟨23,by decide⟩).lower ∧ (cell13067 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13067 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13067 ⟨24,by decide⟩).lower ∧ (cell13067 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13067 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13067 ⟨25,by decide⟩).lower ∧ (cell13067 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13067 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13067 ⟨26,by decide⟩).lower ∧ (cell13067 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13067 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13067 ⟨27,by decide⟩).lower ∧ (cell13067 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13067 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13067 ⟨28,by decide⟩).lower ∧ (cell13067 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13067 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13067 ⟨29,by decide⟩).lower ∧ (cell13067 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13067 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13067 ⟨30,by decide⟩).lower ∧ (cell13067 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13067 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13067 ⟨31,by decide⟩).lower ∧ (cell13067 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13067 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13067 ⟨32,by decide⟩).lower ∧ (cell13067 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13067 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13067 ⟨33,by decide⟩).lower ∧ (cell13067 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13067 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13067 ⟨34,by decide⟩).lower ∧ (cell13067 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13067 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13067 ⟨35,by decide⟩).lower ∧ (cell13067 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13067 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13067 ⟨36,by decide⟩).lower ∧ (cell13067 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13067 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13067 ⟨37,by decide⟩).lower ∧ (cell13067 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13067 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13067 ⟨38,by decide⟩).lower ∧ (cell13067 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13067 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13067 ⟨39,by decide⟩).lower ∧ (cell13067 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13067 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13067 ⟨40,by decide⟩).lower ∧ (cell13067 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13067 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13067 ⟨41,by decide⟩).lower ∧ (cell13067 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13067 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13067 ⟨42,by decide⟩).lower ∧ (cell13067 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13067 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13067 ⟨43,by decide⟩).lower ∧ (cell13067 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13067 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13067 ⟨44,by decide⟩).lower ∧ (cell13067 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13067 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13067 ⟨45,by decide⟩).lower ∧ (cell13067 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13067 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13067 ⟨46,by decide⟩).lower ∧ (cell13067 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13067 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13067 ⟨47,by decide⟩).lower ∧ (cell13067 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13067 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13067 ⟨48,by decide⟩).lower ∧ (cell13067 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13067 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13067 ⟨49,by decide⟩).lower ∧ (cell13067 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13067 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13067 ⟨50,by decide⟩).lower ∧ (cell13067 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13067 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13067 ⟨51,by decide⟩).lower ∧ (cell13067 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13067 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13067 ⟨52,by decide⟩).lower ∧ (cell13067 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13067 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13067 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13067 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13067,cell13067,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13067 i).lower ∧
    (cell13067 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13067 i).upper ≤ (0.532 : ℝ) ∧
    (cell13067 i).centre ≤ (0.1 : ℝ) ∧ (cell13067 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13067 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13067 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13067

/-! The local source numeric instances at 13067 have no network premises. -/
namespace BstLean.Part269.N13067
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13067)
open BstLean.Part268 (cell13067)

noncomputable def sourceNumerics13067 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13067 (cell13067 i)
      scalarRow13067.M scalarRow13067.H scalarRow13067.xi := by
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
    energy_allowance := scalarRow13067.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13067]
    centre_nonneg := (scalarRow13067.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13067])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13067
/-! Actual 13068 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13068 ≤ (1.035297016621 : ℝ) := by
  have hr : (114.315353299545 : ℝ) ≤ √(13068 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.315353299545 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13068 13068 (11 / 1000) ≤
    (0.008361842028 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13068) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.315353299545 : ℝ) ≤ √(13068 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13068)
  have hdiv : K / √(13068 : ℝ) ≤ K / 114.315353299545 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.315353299545 ≤ (0.008361842028 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13068.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13068 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13068 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13068 := gPlus_lower 13068
end BstLean.Part269.N13068

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13068
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035297016620 : ℝ) ≤ wn 13068 := by
  have hn : √(13068 : ℝ) ≤ 114.315353299546 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13068 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.315353299546 ≤ 2 / √(13068 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244666758 : ℝ) ≤ rhoBar 13068 BstLean.Part154.csC ∧
    rhoBar 13068 BstLean.Part154.csC ≤ 0.000244667137 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035297016620 : ℝ) / (1.295212 * 13068) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035297016621 : ℝ) / (1.29521 * 13068) := by gcongr
      _ ≤ (0.000244667137 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13068 BstLean.Part154.csC) ≤ 0.000978728411 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13068 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) ≤ 0.000186878161 ∧
    cc1 (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) ≤ 0.000118911866 ∧
    cc2 (rhoBar 13068 BstLean.Part154.csC) ≤ 0.000069029311 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13068 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13068 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13068 BstLean.Part154.csC * nuR (rhoBar 13068 BstLean.Part154.csC)) ≤ 0.000489349240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244667137 : ℝ) * 0.000978728411 := by gcongr
      _ ≤ (0.000489349240 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13068 BstLean.Part154.csC) * nuR (rhoBar 13068 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978728411 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13068 BstLean.Part154.csC) * rhoBar 13068 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244667137 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244667137 / 2 + 0.399 * 0.000978728411 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186878161 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489349240 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118911866 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244667137 / 1.414213562 := by gcongr
      _ ≤ (0.000069029311 : ℝ) := by norm_num

end BstLean.Part269.N13068

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13068
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) ≤ 1.50818E-7 := by
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13068 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13068 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13068 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186878161 : ℝ) ^ 2 + 0.000118911866 ^ 2 + 3 * 0.000069029311 ^ 2 +
        2 * 0.797885 * 0.000186878161 * 0.000118911866 + 2 * 0.000186878161 * 0.000069029311 +
        4 * 0.797885 * 0.000118911866 * 0.000069029311 := by gcongr
    _ ≤ (1.50818E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13068 BstLean.Part154.csC Θ ≤ 0.002552719900 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13068 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13068 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13068 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035297016621 * 1.50818E-7 / (0.000244666758 : ℝ) := by gcongr
    _ ≤ 0.002552719900 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13068 BstLean.Part154.csC Θ ≤ 0.002830975636 + 0.000645031327 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13068 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13068 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035297016621 : ℝ) * ((2 * Θ * 0.000244667137 +
        (6863 / 10000) * 0.000244667137 * 13068 * 0.000978728411) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002830975636 + 0.000645031327 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13068 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13068 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13068 0.011 Θ ∧ gammaRatio 13068 0.011 Θ ≤ 0.000084110235 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13068 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035297016621 : ℝ) * 0.525 / ((1 - 0.011) * 13068) := by gcongr
      _ ≤ (0.000084110235 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13068 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13068 0.011 Θ) :=
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
    badAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13068 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13068 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13068 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13068 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13068 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13068 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13068 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13068 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13068 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13068 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035297016621 : ℝ) * 13068 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003214725023 + 0.003197751227 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13068

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13068
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13068 BstLean.Part154.csC) (piBar (rhoBar 13068 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13068 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13068 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13068 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13068 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13068 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13068 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13068 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13068 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13068 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13068 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051732090281 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13068) ≤ 0.010446869529 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13068 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035297016621)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010446869529 + 2 * 0.737676 / 13068) := by gcongr
    _ ≤ (0.051732090281 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13068 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13068

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13068
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519741697 : ℝ) ≤ plow 13068 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13068) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400144418)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340177948) : eMP 13068 0.011 xi bn ≤ 0.001154257175 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13068 : ℝ) * (1 - 0.011))) ≤ 0.000570759943 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340177948 / (13068 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570759943 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570759943 : ℝ) + 3.141593 * 0.052400144418 / (13068 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154257175 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400144418)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340177948) : PiBarMP 13068 12 0.011 xi bn ≤ 0.158941971479 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13068 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036608440940 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.684880261185 : ℝ) ≤ √((13068 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.315353299545 : ℝ) ≤ √(13068 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13068) ≤ 0.121876964560 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036608440940 + 0.052400144418 * 1.772454 / (2 * (113.684880261185 : ℝ))) * (1 + 0.001154257175) +
        8 / (13068 * 114.315353299545) + 0.121876964560 := by gcongr
    _ ≤ (0.158941971479 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400144418)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340177948) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280642868573) :
    parallelOracle 13068 0.011 xi bn cd ≤ 0.159904627753 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13068 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13068 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519741697 : ℝ) ≤ plow 13068 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.315353299545 : ℝ) ≤ √(13068 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280642868573 : ℝ) / (2 * 0.560519741697 * 114.315353299545)) * 0.158941971479 +
        0.280642868573 ^ 2 / (2 * 0.560519741697 * 114.315353299545) := by gcongr
    _ ≤ (0.159904627753 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052400144418) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340177948)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280642868573) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13068 13068 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519741697 : ℝ) ≤ plow 13068 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.315353299545 : ℝ) ≤ √(13068 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13068 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13068 Θ 1.22 ≤ 0.011600370919 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.315353299545 := by gcongr <;> linarith
      _ ≤ (0.011600370919 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13068 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13068 13068 0.011 ≤ 0.008361842028 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13068 13068 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13068 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13068 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13068 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13068 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159904627753 + 0.011600370919 + (0.008361842028 : ℝ) *
        (1 + 2 * (0.280642868573 + 0.011600370919) / (0.560519741697 * 114.315353299545))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13068]

end BstLean.Part269.N13068

/-! The original eight local profiles supply actual 13068 moment certificates. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13068 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052400144418 ∧
    0 ≤ bN 13068 BstLean.Part154.csC (groupTheta g) ∧ bN 13068 BstLean.Part154.csC (groupTheta g) ≤ 0.001340177948 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13068 13068 0.011
      (momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13068 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13068 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13068 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228910778292 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13068 0.011
      (momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13068 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13068
/-! The actual computed-centre upper energy formula at 13068. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13068

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13068)
open BstLean.Part268 (cell13068)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084483877851
  | 2 => 0.085410265061
  | 3 => 0.086332519090
  | 4 => 0.087251523779
  | 5 => 0.088168363632
  | 6 => 0.089084355528
  | 7 => 0.090001083765
  | 8 => 0.090920438574
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13068 13068 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13068 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13068

/-! Actual upper energy certificates on all 43 source endpoints at 13068. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13068)
open BstLean.Part268 (cell13068)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13068 (gMinus 13068) (1 - (cell13068 i).lower) ≤ 1 ∧
    energyUpper 13068 (gMinus 13068) (BstLean.Part211.gPlus 13068)
      (finiteEnergy 13068 13068 0.011) (1 - (cell13068 i).lower) ≤
      (cell13068 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨10,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨11,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨12,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨13,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨14,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨15,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨16,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨17,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨18,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨19,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨20,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨21,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨22,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨23,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨24,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨25,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨26,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨27,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨28,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨29,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨30,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨31,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨32,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨33,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨34,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨35,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨36,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨37,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨38,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨39,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨40,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨41,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨42,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨43,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨44,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨45,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨46,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨47,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨48,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨49,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨50,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨51,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13068) (by norm_num)
        (q := 1 - (cell13068 ⟨52,by decide⟩).lower)
        (by norm_num [cell13068]) (by norm_num [cell13068])
      exact ⟨E.1,E.2.trans (by norm_num [cell13068])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13068

/-! Source-cell containment and simple scalar guards at 13068. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13068)
open BstLean.Part268 (cell13068)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13068 ⟨10,by decide⟩).lower ∧ (cell13068 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13068 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13068 ⟨11,by decide⟩).lower ∧ (cell13068 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13068 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13068 ⟨12,by decide⟩).lower ∧ (cell13068 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13068 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13068 ⟨13,by decide⟩).lower ∧ (cell13068 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13068 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13068 ⟨14,by decide⟩).lower ∧ (cell13068 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13068 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13068 ⟨15,by decide⟩).lower ∧ (cell13068 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13068 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13068 ⟨16,by decide⟩).lower ∧ (cell13068 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13068 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13068 ⟨17,by decide⟩).lower ∧ (cell13068 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13068 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13068 ⟨18,by decide⟩).lower ∧ (cell13068 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13068 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13068 ⟨19,by decide⟩).lower ∧ (cell13068 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13068 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13068 ⟨20,by decide⟩).lower ∧ (cell13068 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13068 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13068 ⟨21,by decide⟩).lower ∧ (cell13068 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13068 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13068 ⟨22,by decide⟩).lower ∧ (cell13068 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13068 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13068 ⟨23,by decide⟩).lower ∧ (cell13068 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13068 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13068 ⟨24,by decide⟩).lower ∧ (cell13068 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13068 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13068 ⟨25,by decide⟩).lower ∧ (cell13068 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13068 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13068 ⟨26,by decide⟩).lower ∧ (cell13068 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13068 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13068 ⟨27,by decide⟩).lower ∧ (cell13068 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13068 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13068 ⟨28,by decide⟩).lower ∧ (cell13068 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13068 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13068 ⟨29,by decide⟩).lower ∧ (cell13068 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13068 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13068 ⟨30,by decide⟩).lower ∧ (cell13068 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13068 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13068 ⟨31,by decide⟩).lower ∧ (cell13068 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13068 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13068 ⟨32,by decide⟩).lower ∧ (cell13068 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13068 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13068 ⟨33,by decide⟩).lower ∧ (cell13068 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13068 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13068 ⟨34,by decide⟩).lower ∧ (cell13068 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13068 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13068 ⟨35,by decide⟩).lower ∧ (cell13068 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13068 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13068 ⟨36,by decide⟩).lower ∧ (cell13068 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13068 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13068 ⟨37,by decide⟩).lower ∧ (cell13068 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13068 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13068 ⟨38,by decide⟩).lower ∧ (cell13068 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13068 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13068 ⟨39,by decide⟩).lower ∧ (cell13068 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13068 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13068 ⟨40,by decide⟩).lower ∧ (cell13068 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13068 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13068 ⟨41,by decide⟩).lower ∧ (cell13068 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13068 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13068 ⟨42,by decide⟩).lower ∧ (cell13068 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13068 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13068 ⟨43,by decide⟩).lower ∧ (cell13068 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13068 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13068 ⟨44,by decide⟩).lower ∧ (cell13068 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13068 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13068 ⟨45,by decide⟩).lower ∧ (cell13068 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13068 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13068 ⟨46,by decide⟩).lower ∧ (cell13068 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13068 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13068 ⟨47,by decide⟩).lower ∧ (cell13068 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13068 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13068 ⟨48,by decide⟩).lower ∧ (cell13068 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13068 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13068 ⟨49,by decide⟩).lower ∧ (cell13068 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13068 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13068 ⟨50,by decide⟩).lower ∧ (cell13068 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13068 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13068 ⟨51,by decide⟩).lower ∧ (cell13068 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13068 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13068 ⟨52,by decide⟩).lower ∧ (cell13068 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13068 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13068 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13068 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13068,cell13068,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13068 i).lower ∧
    (cell13068 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13068 i).upper ≤ (0.532 : ℝ) ∧
    (cell13068 i).centre ≤ (0.1 : ℝ) ∧ (cell13068 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13068 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13068 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13068

/-! The local source numeric instances at 13068 have no network premises. -/
namespace BstLean.Part269.N13068
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13068)
open BstLean.Part268 (cell13068)

noncomputable def sourceNumerics13068 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13068 (cell13068 i)
      scalarRow13068.M scalarRow13068.H scalarRow13068.xi := by
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
    energy_allowance := scalarRow13068.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13068]
    centre_nonneg := (scalarRow13068.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13068])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13068
/-! Actual 13069 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13069 ≤ (1.035295654475 : ℝ) := by
  have hr : (114.319727081549 : ℝ) ≤ √(13069 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.319727081549 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13069 13069 (11 / 1000) ≤
    (0.008361522108 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13069) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.319727081549 : ℝ) ≤ √(13069 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13069)
  have hdiv : K / √(13069 : ℝ) ≤ K / 114.319727081549 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.319727081549 ≤ (0.008361522108 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13069.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13069 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13069 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13069 := gPlus_lower 13069
end BstLean.Part269.N13069

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13069
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035295654474 : ℝ) ≤ wn 13069 := by
  have hn : √(13069 : ℝ) ≤ 114.319727081550 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13069 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.319727081550 ≤ 2 / √(13069 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244647715 : ℝ) ≤ rhoBar 13069 BstLean.Part154.csC ∧
    rhoBar 13069 BstLean.Part154.csC ≤ 0.000244648094 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035295654474 : ℝ) / (1.295212 * 13069) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035295654475 : ℝ) / (1.29521 * 13069) := by gcongr
      _ ≤ (0.000244648094 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13069 BstLean.Part154.csC) ≤ 0.000978652229 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13069 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) ≤ 0.000186863615 ∧
    cc1 (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) ≤ 0.000118902610 ∧
    cc2 (rhoBar 13069 BstLean.Part154.csC) ≤ 0.000069023939 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13069 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13069 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13069 BstLean.Part154.csC * nuR (rhoBar 13069 BstLean.Part154.csC)) ≤ 0.000489311152 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244648094 : ℝ) * 0.000978652229 := by gcongr
      _ ≤ (0.000489311152 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13069 BstLean.Part154.csC) * nuR (rhoBar 13069 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978652229 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13069 BstLean.Part154.csC) * rhoBar 13069 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244648094 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244648094 / 2 + 0.399 * 0.000978652229 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186863615 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489311152 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118902610 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244648094 / 1.414213562 := by gcongr
      _ ≤ (0.000069023939 : ℝ) := by norm_num

end BstLean.Part269.N13069

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13069
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) ≤ 1.50794E-7 := by
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13069 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13069 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13069 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186863615 : ℝ) ^ 2 + 0.000118902610 ^ 2 + 3 * 0.000069023939 ^ 2 +
        2 * 0.797885 * 0.000186863615 * 0.000118902610 + 2 * 0.000186863615 * 0.000069023939 +
        4 * 0.797885 * 0.000118902610 * 0.000069023939 := by gcongr
    _ ≤ (1.50794E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13069 BstLean.Part154.csC Θ ≤ 0.002552508990 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13069 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13069 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13069 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035295654475 * 1.50794E-7 / (0.000244647715 : ℝ) := by gcongr
    _ ≤ 0.002552508990 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13069 BstLean.Part154.csC Θ ≤ 0.002830747831 + 0.000644980274 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13069 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13069 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035295654475 : ℝ) * ((2 * Θ * 0.000244648094 +
        (6863 / 10000) * 0.000244648094 * 13069 * 0.000978652229) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002830747831 + 0.000644980274 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13069 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13069 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13069 0.011 Θ ∧ gammaRatio 13069 0.011 Θ ≤ 0.000084103689 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13069 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035295654475 : ℝ) * 0.525 / ((1 - 0.011) * 13069) := by gcongr
      _ ≤ (0.000084103689 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13069 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13069 0.011 Θ) :=
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
    badAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13069 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13069 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13069 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13069 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13069 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13069 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13069 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13069 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13069 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13069 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035295654475 : ℝ) * 13069 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003214497218 + 0.003197489264 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13069

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13069
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13069 BstLean.Part154.csC) (piBar (rhoBar 13069 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13069 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13069 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13069 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13069 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13069 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13069 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13069 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13069 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13069 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13069 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051730089892 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13069) ≤ 0.010446469840 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13069 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035295654475)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010446469840 + 2 * 0.737676 / 13069) := by gcongr
    _ ≤ (0.051730089892 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13069 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13069

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13069
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519784405 : ℝ) ≤ plow 13069 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13069) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399779082)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340067220) : eMP 13069 0.011 xi bn ≤ 0.001154165282 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13069 : ℝ) * (1 - 0.011))) ≤ 0.000570714528 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001340067220 / (13069 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570714528 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570714528 : ℝ) + 3.141593 * 0.052399779082 / (13069 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154165282 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399779082)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340067220) : PiBarMP 13069 12 0.011 xi bn ≤ 0.158935771945 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13069 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036606928580 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.689229920868 : ℝ) ≤ √((13069 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.319727081549 : ℝ) ≤ √(13069 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13069) ≤ 0.121872301645 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036606928580 + 0.052399779082 * 1.772454 / (2 * (113.689229920868 : ℝ))) * (1 + 0.001154165282) +
        8 / (13069 * 114.319727081549) + 0.121872301645 := by gcongr
    _ ≤ (0.158935771945 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399779082)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340067220) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280640070195) :
    parallelOracle 13069 0.011 xi bn cd ≤ 0.159898362013 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13069 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13069 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519784405 : ℝ) ≤ plow 13069 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.319727081549 : ℝ) ≤ √(13069 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280640070195 : ℝ) / (2 * 0.560519784405 * 114.319727081549)) * 0.158935771945 +
        0.280640070195 ^ 2 / (2 * 0.560519784405 * 114.319727081549) := by gcongr
    _ ≤ (0.159898362013 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399779082) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001340067220)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280640070195) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13069 13069 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519784405 : ℝ) ≤ plow 13069 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.319727081549 : ℝ) ≤ √(13069 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13069 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13069 Θ 1.22 ≤ 0.011599927098 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.319727081549 := by gcongr <;> linarith
      _ ≤ (0.011599927098 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13069 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13069 13069 0.011 ≤ 0.008361522108 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13069 13069 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13069 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13069 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13069 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13069 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159898362013 + 0.011599927098 + (0.008361522108 : ℝ) *
        (1 + 2 * (0.280640070195 + 0.011599927098) / (0.560519784405 * 114.319727081549))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13069]

end BstLean.Part269.N13069

/-! The original eight local profiles supply actual 13069 moment certificates. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13069 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052399779082 ∧
    0 ≤ bN 13069 BstLean.Part154.csC (groupTheta g) ∧ bN 13069 BstLean.Part154.csC (groupTheta g) ≤ 0.001340067220 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13069 13069 0.011
      (momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13069 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13069 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13069 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228909980303 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13069 0.011
      (momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13069 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13069
/-! The actual computed-centre upper energy formula at 13069. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13069

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13069)
open BstLean.Part268 (cell13069)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084481312853
  | 2 => 0.085407667372
  | 3 => 0.086329883902
  | 4 => 0.087248845145
  | 5 => 0.088165634261
  | 6 => 0.089081566541
  | 7 => 0.089998224435
  | 8 => 0.090917496020
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13069 13069 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13069 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13069

/-! Actual upper energy certificates on all 43 source endpoints at 13069. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13069)
open BstLean.Part268 (cell13069)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13069 (gMinus 13069) (1 - (cell13069 i).lower) ≤ 1 ∧
    energyUpper 13069 (gMinus 13069) (BstLean.Part211.gPlus 13069)
      (finiteEnergy 13069 13069 0.011) (1 - (cell13069 i).lower) ≤
      (cell13069 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨10,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨11,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨12,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨13,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨14,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨15,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨16,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨17,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨18,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨19,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨20,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨21,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨22,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨23,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨24,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨25,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨26,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨27,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨28,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨29,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨30,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨31,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨32,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨33,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨34,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨35,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨36,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨37,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨38,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨39,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨40,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨41,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨42,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨43,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨44,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨45,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨46,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨47,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨48,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨49,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨50,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨51,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13069) (by norm_num)
        (q := 1 - (cell13069 ⟨52,by decide⟩).lower)
        (by norm_num [cell13069]) (by norm_num [cell13069])
      exact ⟨E.1,E.2.trans (by norm_num [cell13069])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13069

/-! Source-cell containment and simple scalar guards at 13069. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13069)
open BstLean.Part268 (cell13069)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13069 ⟨10,by decide⟩).lower ∧ (cell13069 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13069 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13069 ⟨11,by decide⟩).lower ∧ (cell13069 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13069 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13069 ⟨12,by decide⟩).lower ∧ (cell13069 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13069 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13069 ⟨13,by decide⟩).lower ∧ (cell13069 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13069 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13069 ⟨14,by decide⟩).lower ∧ (cell13069 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13069 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13069 ⟨15,by decide⟩).lower ∧ (cell13069 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13069 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13069 ⟨16,by decide⟩).lower ∧ (cell13069 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13069 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13069 ⟨17,by decide⟩).lower ∧ (cell13069 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13069 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13069 ⟨18,by decide⟩).lower ∧ (cell13069 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13069 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13069 ⟨19,by decide⟩).lower ∧ (cell13069 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13069 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13069 ⟨20,by decide⟩).lower ∧ (cell13069 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13069 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13069 ⟨21,by decide⟩).lower ∧ (cell13069 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13069 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13069 ⟨22,by decide⟩).lower ∧ (cell13069 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13069 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13069 ⟨23,by decide⟩).lower ∧ (cell13069 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13069 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13069 ⟨24,by decide⟩).lower ∧ (cell13069 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13069 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13069 ⟨25,by decide⟩).lower ∧ (cell13069 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13069 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13069 ⟨26,by decide⟩).lower ∧ (cell13069 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13069 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13069 ⟨27,by decide⟩).lower ∧ (cell13069 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13069 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13069 ⟨28,by decide⟩).lower ∧ (cell13069 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13069 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13069 ⟨29,by decide⟩).lower ∧ (cell13069 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13069 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13069 ⟨30,by decide⟩).lower ∧ (cell13069 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13069 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13069 ⟨31,by decide⟩).lower ∧ (cell13069 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13069 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13069 ⟨32,by decide⟩).lower ∧ (cell13069 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13069 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13069 ⟨33,by decide⟩).lower ∧ (cell13069 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13069 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13069 ⟨34,by decide⟩).lower ∧ (cell13069 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13069 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13069 ⟨35,by decide⟩).lower ∧ (cell13069 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13069 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13069 ⟨36,by decide⟩).lower ∧ (cell13069 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13069 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13069 ⟨37,by decide⟩).lower ∧ (cell13069 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13069 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13069 ⟨38,by decide⟩).lower ∧ (cell13069 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13069 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13069 ⟨39,by decide⟩).lower ∧ (cell13069 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13069 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13069 ⟨40,by decide⟩).lower ∧ (cell13069 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13069 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13069 ⟨41,by decide⟩).lower ∧ (cell13069 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13069 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13069 ⟨42,by decide⟩).lower ∧ (cell13069 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13069 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13069 ⟨43,by decide⟩).lower ∧ (cell13069 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13069 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13069 ⟨44,by decide⟩).lower ∧ (cell13069 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13069 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13069 ⟨45,by decide⟩).lower ∧ (cell13069 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13069 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13069 ⟨46,by decide⟩).lower ∧ (cell13069 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13069 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13069 ⟨47,by decide⟩).lower ∧ (cell13069 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13069 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13069 ⟨48,by decide⟩).lower ∧ (cell13069 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13069 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13069 ⟨49,by decide⟩).lower ∧ (cell13069 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13069 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13069 ⟨50,by decide⟩).lower ∧ (cell13069 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13069 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13069 ⟨51,by decide⟩).lower ∧ (cell13069 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13069 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13069 ⟨52,by decide⟩).lower ∧ (cell13069 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13069 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13069 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13069 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13069,cell13069,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13069 i).lower ∧
    (cell13069 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13069 i).upper ≤ (0.532 : ℝ) ∧
    (cell13069 i).centre ≤ (0.1 : ℝ) ∧ (cell13069 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13069 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13069 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13069

/-! The local source numeric instances at 13069 have no network premises. -/
namespace BstLean.Part269.N13069
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13069)
open BstLean.Part268 (cell13069)

noncomputable def sourceNumerics13069 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13069 (cell13069 i)
      scalarRow13069.M scalarRow13069.H scalarRow13069.xi := by
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
    energy_allowance := scalarRow13069.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13069]
    centre_nonneg := (scalarRow13069.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13069])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13069
/-! Actual 13070 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13070 ≤ (1.035294292486 : ℝ) := by
  have hr : (114.324100696222 : ℝ) ≤ √(13070 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.324100696222 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13070 13070 (11 / 1000) ≤
    (0.008361202225 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13070) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.324100696222 : ℝ) ≤ √(13070 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13070)
  have hdiv : K / √(13070 : ℝ) ≤ K / 114.324100696222 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.324100696222 ≤ (0.008361202225 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13070.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13070 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13070 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13070 := gPlus_lower 13070
end BstLean.Part269.N13070

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13070
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035294292485 : ℝ) ≤ wn 13070 := by
  have hn : √(13070 : ℝ) ≤ 114.324100696223 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13070 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.324100696223 ≤ 2 / √(13070 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244628675 : ℝ) ≤ rhoBar 13070 BstLean.Part154.csC ∧
    rhoBar 13070 BstLean.Part154.csC ≤ 0.000244629054 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035294292485 : ℝ) / (1.295212 * 13070) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035294292486 : ℝ) / (1.29521 * 13070) := by gcongr
      _ ≤ (0.000244629054 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13070 BstLean.Part154.csC) ≤ 0.000978576060 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13070 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) ≤ 0.000186849072 ∧
    cc1 (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) ≤ 0.000118893356 ∧
    cc2 (rhoBar 13070 BstLean.Part154.csC) ≤ 0.000069018567 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13070 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13070 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13070 BstLean.Part154.csC * nuR (rhoBar 13070 BstLean.Part154.csC)) ≤ 0.000489273069 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244629054 : ℝ) * 0.000978576060 := by gcongr
      _ ≤ (0.000489273069 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13070 BstLean.Part154.csC) * nuR (rhoBar 13070 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978576060 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13070 BstLean.Part154.csC) * rhoBar 13070 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244629054 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244629054 / 2 + 0.399 * 0.000978576060 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186849072 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489273069 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118893356 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244629054 / 1.414213562 := by gcongr
      _ ≤ (0.000069018567 : ℝ) := by norm_num

end BstLean.Part269.N13070

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13070
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) ≤ 1.50771E-7 := by
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13070 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13070 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13070 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186849072 : ℝ) ^ 2 + 0.000118893356 ^ 2 + 3 * 0.000069018567 ^ 2 +
        2 * 0.797885 * 0.000186849072 * 0.000118893356 + 2 * 0.000186849072 * 0.000069018567 +
        4 * 0.797885 * 0.000118893356 * 0.000069018567 := by gcongr
    _ ≤ (1.50771E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13070 BstLean.Part154.csC Θ ≤ 0.002552314945 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13070 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13070 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13070 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035294292486 * 1.50771E-7 / (0.000244628675 : ℝ) := by gcongr
    _ ≤ 0.002552314945 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13070 BstLean.Part154.csC Θ ≤ 0.002830520067 + 0.000644929230 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13070 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13070 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035294292486 : ℝ) * ((2 * Θ * 0.000244629054 +
        (6863 / 10000) * 0.000244629054 * 13070 * 0.000978576060) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002830520067 + 0.000644929230 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13070 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13070 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13070 0.011 Θ ∧ gammaRatio 13070 0.011 Θ ≤ 0.000084097143 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13070 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035294292486 : ℝ) * 0.525 / ((1 - 0.011) * 13070) := by gcongr
      _ ≤ (0.000084097143 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13070 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13070 0.011 Θ) :=
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
    badAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13070 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13070 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13070 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13070 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13070 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13070 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13070 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13070 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13070 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13070 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035294292486 : ℝ) * 13070 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003214269454 + 0.003197244175 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13070

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13070
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13070 BstLean.Part154.csC) (piBar (rhoBar 13070 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13070 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13070 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13070 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13070 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13070 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13070 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13070 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13070 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13070 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13070 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051728089735 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13070) ≤ 0.010446070197 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13070 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035294292486)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010446070197 + 2 * 0.737676 / 13070) := by gcongr
    _ ≤ (0.051728089735 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13070 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13070

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13070
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519827107 : ℝ) ≤ plow 13070 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13070) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399422646)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339965347) : eMP 13070 0.011 xi bn ≤ 0.001154077169 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13070 : ℝ) * (1 - 0.011))) ≤ 0.000570671002 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339965347 / (13070 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570671002 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570671002 : ℝ) + 3.141593 * 0.052399422646 / (13070 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001154077169 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399422646)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339965347) : PiBarMP 13070 12 0.011 xi bn ≤ 0.158929694185 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13070 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036605537109 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.693579414142 : ℝ) ≤ √((13070 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.324100696222 : ℝ) ≤ √(13070 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13070) ≤ 0.121867639264 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036605537109 + 0.052399422646 * 1.772454 / (2 * (113.693579414142 : ℝ))) * (1 + 0.001154077169) +
        8 / (13070 * 114.324100696222) + 0.121867639264 := by gcongr
    _ ≤ (0.158929694185 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399422646)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339965347) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280637291486) :
    parallelOracle 13070 0.011 xi bn cd ≤ 0.159892218431 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13070 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13070 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519827107 : ℝ) ≤ plow 13070 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.324100696222 : ℝ) ≤ √(13070 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280637291486 : ℝ) / (2 * 0.560519827107 * 114.324100696222)) * 0.158929694185 +
        0.280637291486 ^ 2 / (2 * 0.560519827107 * 114.324100696222) := by gcongr
    _ ≤ (0.159892218431 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399422646) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339965347)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280637291486) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13070 13070 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519827107 : ℝ) ≤ plow 13070 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.324100696222 : ℝ) ≤ √(13070 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13070 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13070 Θ 1.22 ≤ 0.011599483328 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.324100696222 := by gcongr <;> linarith
      _ ≤ (0.011599483328 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13070 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13070 13070 0.011 ≤ 0.008361202225 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13070 13070 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13070 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13070 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13070 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13070 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159892218431 + 0.011599483328 + (0.008361202225 : ℝ) *
        (1 + 2 * (0.280637291486 + 0.011599483328) / (0.560519827107 * 114.324100696222))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13070]

end BstLean.Part269.N13070

/-! The original eight local profiles supply actual 13070 moment certificates. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13070 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052399422646 ∧
    0 ≤ bN 13070 BstLean.Part154.csC (groupTheta g) ∧ bN 13070 BstLean.Part154.csC (groupTheta g) ≤ 0.001339965347 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13070 13070 0.011
      (momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13070 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13070 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13070 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228909201751 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13070 0.011
      (momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13070 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13070
/-! The actual computed-centre upper energy formula at 13070. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13070

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13070)
open BstLean.Part268 (cell13070)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084478748613
  | 2 => 0.085405070467
  | 3 => 0.086327249530
  | 4 => 0.087246167368
  | 5 => 0.088162905795
  | 6 => 0.089078778520
  | 7 => 0.089995366143
  | 8 => 0.090914554593
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13070 13070 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13070 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13070

/-! Actual upper energy certificates on all 43 source endpoints at 13070. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13070)
open BstLean.Part268 (cell13070)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13070 (gMinus 13070) (1 - (cell13070 i).lower) ≤ 1 ∧
    energyUpper 13070 (gMinus 13070) (BstLean.Part211.gPlus 13070)
      (finiteEnergy 13070 13070 0.011) (1 - (cell13070 i).lower) ≤
      (cell13070 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨10,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨11,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨12,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨13,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨14,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨15,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨16,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨17,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨18,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨19,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨20,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨21,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨22,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨23,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨24,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨25,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨26,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨27,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨28,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨29,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨30,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨31,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨32,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨33,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨34,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨35,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨36,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨37,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨38,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨39,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨40,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨41,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨42,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨43,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨44,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨45,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨46,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨47,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨48,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨49,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨50,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨51,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13070) (by norm_num)
        (q := 1 - (cell13070 ⟨52,by decide⟩).lower)
        (by norm_num [cell13070]) (by norm_num [cell13070])
      exact ⟨E.1,E.2.trans (by norm_num [cell13070])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13070

/-! Source-cell containment and simple scalar guards at 13070. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13070)
open BstLean.Part268 (cell13070)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13070 ⟨10,by decide⟩).lower ∧ (cell13070 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13070 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13070 ⟨11,by decide⟩).lower ∧ (cell13070 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13070 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13070 ⟨12,by decide⟩).lower ∧ (cell13070 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13070 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13070 ⟨13,by decide⟩).lower ∧ (cell13070 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13070 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13070 ⟨14,by decide⟩).lower ∧ (cell13070 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13070 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13070 ⟨15,by decide⟩).lower ∧ (cell13070 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13070 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13070 ⟨16,by decide⟩).lower ∧ (cell13070 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13070 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13070 ⟨17,by decide⟩).lower ∧ (cell13070 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13070 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13070 ⟨18,by decide⟩).lower ∧ (cell13070 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13070 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13070 ⟨19,by decide⟩).lower ∧ (cell13070 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13070 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13070 ⟨20,by decide⟩).lower ∧ (cell13070 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13070 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13070 ⟨21,by decide⟩).lower ∧ (cell13070 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13070 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13070 ⟨22,by decide⟩).lower ∧ (cell13070 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13070 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13070 ⟨23,by decide⟩).lower ∧ (cell13070 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13070 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13070 ⟨24,by decide⟩).lower ∧ (cell13070 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13070 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13070 ⟨25,by decide⟩).lower ∧ (cell13070 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13070 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13070 ⟨26,by decide⟩).lower ∧ (cell13070 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13070 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13070 ⟨27,by decide⟩).lower ∧ (cell13070 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13070 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13070 ⟨28,by decide⟩).lower ∧ (cell13070 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13070 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13070 ⟨29,by decide⟩).lower ∧ (cell13070 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13070 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13070 ⟨30,by decide⟩).lower ∧ (cell13070 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13070 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13070 ⟨31,by decide⟩).lower ∧ (cell13070 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13070 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13070 ⟨32,by decide⟩).lower ∧ (cell13070 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13070 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13070 ⟨33,by decide⟩).lower ∧ (cell13070 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13070 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13070 ⟨34,by decide⟩).lower ∧ (cell13070 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13070 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13070 ⟨35,by decide⟩).lower ∧ (cell13070 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13070 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13070 ⟨36,by decide⟩).lower ∧ (cell13070 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13070 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13070 ⟨37,by decide⟩).lower ∧ (cell13070 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13070 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13070 ⟨38,by decide⟩).lower ∧ (cell13070 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13070 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13070 ⟨39,by decide⟩).lower ∧ (cell13070 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13070 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13070 ⟨40,by decide⟩).lower ∧ (cell13070 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13070 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13070 ⟨41,by decide⟩).lower ∧ (cell13070 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13070 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13070 ⟨42,by decide⟩).lower ∧ (cell13070 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13070 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13070 ⟨43,by decide⟩).lower ∧ (cell13070 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13070 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13070 ⟨44,by decide⟩).lower ∧ (cell13070 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13070 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13070 ⟨45,by decide⟩).lower ∧ (cell13070 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13070 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13070 ⟨46,by decide⟩).lower ∧ (cell13070 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13070 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13070 ⟨47,by decide⟩).lower ∧ (cell13070 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13070 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13070 ⟨48,by decide⟩).lower ∧ (cell13070 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13070 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13070 ⟨49,by decide⟩).lower ∧ (cell13070 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13070 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13070 ⟨50,by decide⟩).lower ∧ (cell13070 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13070 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13070 ⟨51,by decide⟩).lower ∧ (cell13070 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13070 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13070 ⟨52,by decide⟩).lower ∧ (cell13070 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13070 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13070 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13070 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13070,cell13070,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13070 i).lower ∧
    (cell13070 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13070 i).upper ≤ (0.532 : ℝ) ∧
    (cell13070 i).centre ≤ (0.1 : ℝ) ∧ (cell13070 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13070 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13070 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13070

/-! The local source numeric instances at 13070 have no network premises. -/
namespace BstLean.Part269.N13070
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13070)
open BstLean.Part268 (cell13070)

noncomputable def sourceNumerics13070 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13070 (cell13070 i)
      scalarRow13070.M scalarRow13070.H scalarRow13070.xi := by
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
    energy_allowance := scalarRow13070.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13070]
    centre_nonneg := (scalarRow13070.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13070])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13070
/-! Actual 13071 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13071 ≤ (1.035292930654 : ℝ) := by
  have hr : (114.328474143583 : ℝ) ≤ √(13071 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.328474143583 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13071 13071 (11 / 1000) ≤
    (0.008360882378 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13071) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.328474143583 : ℝ) ≤ √(13071 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13071)
  have hdiv : K / √(13071 : ℝ) ≤ K / 114.328474143583 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.328474143583 ≤ (0.008360882378 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13071.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13071 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13071 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13071 := gPlus_lower 13071
end BstLean.Part269.N13071

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13071
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035292930653 : ℝ) ≤ wn 13071 := by
  have hn : √(13071 : ℝ) ≤ 114.328474143584 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13071 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.328474143584 ≤ 2 / √(13071 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244609638 : ℝ) ≤ rhoBar 13071 BstLean.Part154.csC ∧
    rhoBar 13071 BstLean.Part154.csC ≤ 0.000244610017 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035292930653 : ℝ) / (1.295212 * 13071) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035292930654 : ℝ) / (1.29521 * 13071) := by gcongr
      _ ≤ (0.000244610017 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13071 BstLean.Part154.csC) ≤ 0.000978499903 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13071 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) ≤ 0.000186834530 ∧
    cc1 (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) ≤ 0.000118884104 ∧
    cc2 (rhoBar 13071 BstLean.Part154.csC) ≤ 0.000069013196 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13071 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13071 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13071 BstLean.Part154.csC * nuR (rhoBar 13071 BstLean.Part154.csC)) ≤ 0.000489234993 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244610017 : ℝ) * 0.000978499903 := by gcongr
      _ ≤ (0.000489234993 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13071 BstLean.Part154.csC) * nuR (rhoBar 13071 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978499903 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13071 BstLean.Part154.csC) * rhoBar 13071 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244610017 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244610017 / 2 + 0.399 * 0.000978499903 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186834530 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489234993 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118884104 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244610017 / 1.414213562 := by gcongr
      _ ≤ (0.000069013196 : ℝ) := by norm_num

end BstLean.Part269.N13071

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13071
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) ≤ 1.50748E-7 := by
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13071 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13071 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13071 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186834530 : ℝ) ^ 2 + 0.000118884104 ^ 2 + 3 * 0.000069013196 ^ 2 +
        2 * 0.797885 * 0.000186834530 * 0.000118884104 + 2 * 0.000186834530 * 0.000069013196 +
        4 * 0.797885 * 0.000118884104 * 0.000069013196 := by gcongr
    _ ≤ (1.50748E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13071 BstLean.Part154.csC Θ ≤ 0.002552120841 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13071 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13071 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13071 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035292930654 * 1.50748E-7 / (0.000244609638 : ℝ) := by gcongr
    _ ≤ 0.002552120841 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13071 BstLean.Part154.csC Θ ≤ 0.002830292339 + 0.000644878193 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13071 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13071 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035292930654 : ℝ) * ((2 * Θ * 0.000244610017 +
        (6863 / 10000) * 0.000244610017 * 13071 * 0.000978499903) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002830292339 + 0.000644878193 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13071 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13071 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13071 0.011 Θ ∧ gammaRatio 13071 0.011 Θ ≤ 0.000084090599 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13071 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035292930654 : ℝ) * 0.525 / ((1 - 0.011) * 13071) := by gcongr
      _ ≤ (0.000084090599 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13071 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13071 0.011 Θ) :=
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
    badAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13071 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13071 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13071 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13071 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13071 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13071 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13071 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13071 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13071 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13071 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035292930654 : ℝ) * 13071 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003214041726 + 0.003196999034 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13071

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13071
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13071 BstLean.Part154.csC) (piBar (rhoBar 13071 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13071 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13071 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13071 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13071 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13071 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13071 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13071 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13071 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13071 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13071 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051726089810 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13071) ≤ 0.010445670600 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13071 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035292930654)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010445670600 + 2 * 0.737676 / 13071) := by gcongr
    _ ≤ (0.051726089810 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13071 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13071

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13071
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519869803 : ℝ) ≤ plow 13071 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13071) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399066219)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339863442) : eMP 13071 0.011 xi bn ≤ 0.001153989048 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13071 : ℝ) * (1 - 0.011))) ≤ 0.000570627472 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339863442 / (13071 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570627472 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570627472 : ℝ) + 3.141593 * 0.052399066219 / (13071 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153989048 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399066219)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339863442) : PiBarMP 13071 12 0.011 xi bn ≤ 0.158923616471 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13071 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036604145148 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.697928741028 : ℝ) ≤ √((13071 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.328474143583 : ℝ) ≤ √(13071 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13071) ≤ 0.121862977418 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036604145148 + 0.052399066219 * 1.772454 / (2 * (113.697928741028 : ℝ))) * (1 + 0.001153989048) +
        8 / (13071 * 114.328474143583) + 0.121862977418 := by gcongr
    _ ≤ (0.158923616471 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399066219)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339863442) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280634513026) :
    parallelOracle 13071 0.011 xi bn cd ≤ 0.159886074903 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13071 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13071 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519869803 : ℝ) ≤ plow 13071 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.328474143583 : ℝ) ≤ √(13071 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280634513026 : ℝ) / (2 * 0.560519869803 * 114.328474143583)) * 0.158923616471 +
        0.280634513026 ^ 2 / (2 * 0.560519869803 * 114.328474143583) := by gcongr
    _ ≤ (0.159886074903 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052399066219) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339863442)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280634513026) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13071 13071 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519869803 : ℝ) ≤ plow 13071 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.328474143583 : ℝ) ≤ √(13071 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13071 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13071 Θ 1.22 ≤ 0.011599039609 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.328474143583 := by gcongr <;> linarith
      _ ≤ (0.011599039609 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13071 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13071 13071 0.011 ≤ 0.008360882378 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13071 13071 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13071 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13071 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13071 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13071 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159886074903 + 0.011599039609 + (0.008360882378 : ℝ) *
        (1 + 2 * (0.280634513026 + 0.011599039609) / (0.560519869803 * 114.328474143583))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13071]

end BstLean.Part269.N13071

/-! The original eight local profiles supply actual 13071 moment certificates. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13071 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052399066219 ∧
    0 ≤ bN 13071 BstLean.Part154.csC (groupTheta g) ∧ bN 13071 BstLean.Part154.csC (groupTheta g) ≤ 0.001339863442 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13071 13071 0.011
      (momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13071 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13071 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13071 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228908423216 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13071 0.011
      (momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13071 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13071
/-! The actual computed-centre upper energy formula at 13071. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13071

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13071)
open BstLean.Part268 (cell13071)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084476185132
  | 2 => 0.085402474347
  | 3 => 0.086324615975
  | 4 => 0.087243490447
  | 5 => 0.088160178234
  | 6 => 0.089075991464
  | 7 => 0.089992508889
  | 8 => 0.090911614292
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13071 13071 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13071 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13071

/-! Actual upper energy certificates on all 43 source endpoints at 13071. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13071)
open BstLean.Part268 (cell13071)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13071 (gMinus 13071) (1 - (cell13071 i).lower) ≤ 1 ∧
    energyUpper 13071 (gMinus 13071) (BstLean.Part211.gPlus 13071)
      (finiteEnergy 13071 13071 0.011) (1 - (cell13071 i).lower) ≤
      (cell13071 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨10,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨11,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨12,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨13,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨14,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨15,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨16,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨17,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨18,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨19,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨20,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨21,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨22,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨23,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨24,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨25,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨26,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨27,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨28,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨29,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨30,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨31,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨32,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨33,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨34,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨35,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨36,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨37,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨38,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨39,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨40,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨41,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨42,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨43,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨44,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨45,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨46,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨47,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨48,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨49,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨50,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨51,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13071) (by norm_num)
        (q := 1 - (cell13071 ⟨52,by decide⟩).lower)
        (by norm_num [cell13071]) (by norm_num [cell13071])
      exact ⟨E.1,E.2.trans (by norm_num [cell13071])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13071

/-! Source-cell containment and simple scalar guards at 13071. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13071)
open BstLean.Part268 (cell13071)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13071 ⟨10,by decide⟩).lower ∧ (cell13071 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13071 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13071 ⟨11,by decide⟩).lower ∧ (cell13071 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13071 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13071 ⟨12,by decide⟩).lower ∧ (cell13071 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13071 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13071 ⟨13,by decide⟩).lower ∧ (cell13071 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13071 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13071 ⟨14,by decide⟩).lower ∧ (cell13071 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13071 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13071 ⟨15,by decide⟩).lower ∧ (cell13071 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13071 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13071 ⟨16,by decide⟩).lower ∧ (cell13071 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13071 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13071 ⟨17,by decide⟩).lower ∧ (cell13071 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13071 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13071 ⟨18,by decide⟩).lower ∧ (cell13071 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13071 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13071 ⟨19,by decide⟩).lower ∧ (cell13071 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13071 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13071 ⟨20,by decide⟩).lower ∧ (cell13071 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13071 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13071 ⟨21,by decide⟩).lower ∧ (cell13071 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13071 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13071 ⟨22,by decide⟩).lower ∧ (cell13071 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13071 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13071 ⟨23,by decide⟩).lower ∧ (cell13071 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13071 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13071 ⟨24,by decide⟩).lower ∧ (cell13071 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13071 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13071 ⟨25,by decide⟩).lower ∧ (cell13071 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13071 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13071 ⟨26,by decide⟩).lower ∧ (cell13071 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13071 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13071 ⟨27,by decide⟩).lower ∧ (cell13071 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13071 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13071 ⟨28,by decide⟩).lower ∧ (cell13071 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13071 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13071 ⟨29,by decide⟩).lower ∧ (cell13071 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13071 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13071 ⟨30,by decide⟩).lower ∧ (cell13071 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13071 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13071 ⟨31,by decide⟩).lower ∧ (cell13071 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13071 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13071 ⟨32,by decide⟩).lower ∧ (cell13071 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13071 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13071 ⟨33,by decide⟩).lower ∧ (cell13071 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13071 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13071 ⟨34,by decide⟩).lower ∧ (cell13071 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13071 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13071 ⟨35,by decide⟩).lower ∧ (cell13071 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13071 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13071 ⟨36,by decide⟩).lower ∧ (cell13071 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13071 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13071 ⟨37,by decide⟩).lower ∧ (cell13071 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13071 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13071 ⟨38,by decide⟩).lower ∧ (cell13071 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13071 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13071 ⟨39,by decide⟩).lower ∧ (cell13071 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13071 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13071 ⟨40,by decide⟩).lower ∧ (cell13071 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13071 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13071 ⟨41,by decide⟩).lower ∧ (cell13071 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13071 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13071 ⟨42,by decide⟩).lower ∧ (cell13071 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13071 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13071 ⟨43,by decide⟩).lower ∧ (cell13071 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13071 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13071 ⟨44,by decide⟩).lower ∧ (cell13071 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13071 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13071 ⟨45,by decide⟩).lower ∧ (cell13071 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13071 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13071 ⟨46,by decide⟩).lower ∧ (cell13071 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13071 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13071 ⟨47,by decide⟩).lower ∧ (cell13071 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13071 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13071 ⟨48,by decide⟩).lower ∧ (cell13071 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13071 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13071 ⟨49,by decide⟩).lower ∧ (cell13071 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13071 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13071 ⟨50,by decide⟩).lower ∧ (cell13071 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13071 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13071 ⟨51,by decide⟩).lower ∧ (cell13071 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13071 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13071 ⟨52,by decide⟩).lower ∧ (cell13071 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13071 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13071 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13071 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13071,cell13071,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13071 i).lower ∧
    (cell13071 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13071 i).upper ≤ (0.532 : ℝ) ∧
    (cell13071 i).centre ≤ (0.1 : ℝ) ∧ (cell13071 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13071 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13071 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13071

/-! The local source numeric instances at 13071 have no network premises. -/
namespace BstLean.Part269.N13071
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13071)
open BstLean.Part268 (cell13071)

noncomputable def sourceNumerics13071 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13071 (cell13071 i)
      scalarRow13071.M scalarRow13071.H scalarRow13071.xi := by
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
    energy_allowance := scalarRow13071.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13071]
    centre_nonneg := (scalarRow13071.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13071])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13071
/-! Actual 13072 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13072 ≤ (1.035291568980 : ℝ) := by
  have hr : (114.332847423651 : ℝ) ≤ √(13072 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.332847423651 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13072 13072 (11 / 1000) ≤
    (0.008360562569 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13072) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.332847423651 : ℝ) ≤ √(13072 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13072)
  have hdiv : K / √(13072 : ℝ) ≤ K / 114.332847423651 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.332847423651 ≤ (0.008360562569 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13072.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13072 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13072 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13072 := gPlus_lower 13072
end BstLean.Part269.N13072

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13072
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035291568979 : ℝ) ≤ wn 13072 := by
  have hn : √(13072 : ℝ) ≤ 114.332847423652 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13072 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.332847423652 ≤ 2 / √(13072 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244590604 : ℝ) ≤ rhoBar 13072 BstLean.Part154.csC ∧
    rhoBar 13072 BstLean.Part154.csC ≤ 0.000244590982 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035291568979 : ℝ) / (1.295212 * 13072) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035291568980 : ℝ) / (1.29521 * 13072) := by gcongr
      _ ≤ (0.000244590982 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13072 BstLean.Part154.csC) ≤ 0.000978423753 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13072 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) ≤ 0.000186819991 ∧
    cc1 (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) ≤ 0.000118874852 ∧
    cc2 (rhoBar 13072 BstLean.Part154.csC) ≤ 0.000069007825 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13072 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13072 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13072 BstLean.Part154.csC * nuR (rhoBar 13072 BstLean.Part154.csC)) ≤ 0.000489196921 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244590982 : ℝ) * 0.000978423753 := by gcongr
      _ ≤ (0.000489196921 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13072 BstLean.Part154.csC) * nuR (rhoBar 13072 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978423753 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13072 BstLean.Part154.csC) * rhoBar 13072 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244590982 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244590982 / 2 + 0.399 * 0.000978423753 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186819991 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489196921 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118874852 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244590982 / 1.414213562 := by gcongr
      _ ≤ (0.000069007825 : ℝ) := by norm_num

end BstLean.Part269.N13072

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13072
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) ≤ 1.50724E-7 := by
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13072 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13072 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13072 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186819991 : ℝ) ^ 2 + 0.000118874852 ^ 2 + 3 * 0.000069007825 ^ 2 +
        2 * 0.797885 * 0.000186819991 * 0.000118874852 + 2 * 0.000186819991 * 0.000069007825 +
        4 * 0.797885 * 0.000118874852 * 0.000069007825 := by gcongr
    _ ≤ (1.50724E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13072 BstLean.Part154.csC Θ ≤ 0.002551909745 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13072 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13072 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13072 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035291568980 * 1.50724E-7 / (0.000244590604 : ℝ) := by gcongr
    _ ≤ 0.002551909745 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13072 BstLean.Part154.csC Θ ≤ 0.002830064623 + 0.000644827162 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13072 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13072 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035291568980 : ℝ) * ((2 * Θ * 0.000244590982 +
        (6863 / 10000) * 0.000244590982 * 13072 * 0.000978423753) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002830064623 + 0.000644827162 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13072 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13072 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13072 0.011 Θ ∧ gammaRatio 13072 0.011 Θ ≤ 0.000084084055 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13072 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035291568980 : ℝ) * 0.525 / ((1 - 0.011) * 13072) := by gcongr
      _ ≤ (0.000084084055 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13072 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13072 0.011 Θ) :=
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
    badAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13072 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13072 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13072 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13072 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13072 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13072 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13072 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13072 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13072 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13072 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035291568980 : ℝ) * 13072 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003213814010 + 0.003196736907 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13072

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13072
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13072 BstLean.Part154.csC) (piBar (rhoBar 13072 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13072 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13072 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13072 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13072 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13072 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13072 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13072 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13072 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13072 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13072 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051724090116 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13072) ≤ 0.010445271049 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13072 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035291568980)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010445271049 + 2 * 0.737676 / 13072) := by gcongr
    _ ≤ (0.051724090116 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13072 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13072

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13072
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519912492 : ℝ) ≤ plow 13072 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13072) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398700887)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339752617) : eMP 13072 0.011 xi bn ≤ 0.001153897133 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13072 : ℝ) * (1 - 0.011))) ≤ 0.000570582046 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339752617 / (13072 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570582046 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570582046 : ℝ) + 3.141593 * 0.052398700887 / (13072 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153897133 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398700887)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339752617) : PiBarMP 13072 12 0.011 xi bn ≤ 0.158917417044 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13072 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036602631286 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.702277901544 : ℝ) ≤ √((13072 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.332847423651 : ℝ) ≤ √(13072 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13072) ≤ 0.121858316107 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036602631286 + 0.052398700887 * 1.772454 / (2 * (113.702277901544 : ℝ))) * (1 + 0.001153897133) +
        8 / (13072 * 114.332847423651) + 0.121858316107 := by gcongr
    _ ≤ (0.158917417044 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398700887)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339752617) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280631715343) :
    parallelOracle 13072 0.011 xi bn cd ≤ 0.159879809295 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13072 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13072 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519912492 : ℝ) ≤ plow 13072 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.332847423651 : ℝ) ≤ √(13072 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280631715343 : ℝ) / (2 * 0.560519912492 * 114.332847423651)) * 0.158917417044 +
        0.280631715343 ^ 2 / (2 * 0.560519912492 * 114.332847423651) := by gcongr
    _ ≤ (0.159879809295 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398700887) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339752617)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280631715343) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13072 13072 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519912492 : ℝ) ≤ plow 13072 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.332847423651 : ℝ) ≤ √(13072 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13072 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13072 Θ 1.22 ≤ 0.011598595941 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.332847423651 := by gcongr <;> linarith
      _ ≤ (0.011598595941 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13072 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13072 13072 0.011 ≤ 0.008360562569 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13072 13072 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13072 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13072 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13072 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13072 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159879809295 + 0.011598595941 + (0.008360562569 : ℝ) *
        (1 + 2 * (0.280631715343 + 0.011598595941) / (0.560519912492 * 114.332847423651))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13072]

end BstLean.Part269.N13072

/-! The original eight local profiles supply actual 13072 moment certificates. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13072 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052398700887 ∧
    0 ≤ bN 13072 BstLean.Part154.csC (groupTheta g) ∧ bN 13072 BstLean.Part154.csC (groupTheta g) ≤ 0.001339752617 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13072 13072 0.011
      (momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13072 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13072 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13072 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228907625227 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13072 0.011
      (momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13072 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13072
/-! The actual computed-centre upper energy formula at 13072. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13072

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13072)
open BstLean.Part268 (cell13072)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084473622406
  | 2 => 0.085399879009
  | 3 => 0.086321983235
  | 4 => 0.087240814382
  | 5 => 0.088157451577
  | 6 => 0.089073205372
  | 7 => 0.089989652672
  | 8 => 0.090908675117
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13072 13072 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13072 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13072

/-! Actual upper energy certificates on all 43 source endpoints at 13072. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13072)
open BstLean.Part268 (cell13072)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13072 (gMinus 13072) (1 - (cell13072 i).lower) ≤ 1 ∧
    energyUpper 13072 (gMinus 13072) (BstLean.Part211.gPlus 13072)
      (finiteEnergy 13072 13072 0.011) (1 - (cell13072 i).lower) ≤
      (cell13072 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨10,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨11,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨12,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨13,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨14,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨15,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨16,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨17,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨18,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨19,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨20,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨21,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨22,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨23,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨24,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨25,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨26,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨27,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨28,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨29,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨30,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨31,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨32,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨33,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨34,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨35,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨36,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨37,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨38,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨39,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨40,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨41,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨42,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨43,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨44,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨45,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨46,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨47,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨48,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨49,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨50,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨51,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13072) (by norm_num)
        (q := 1 - (cell13072 ⟨52,by decide⟩).lower)
        (by norm_num [cell13072]) (by norm_num [cell13072])
      exact ⟨E.1,E.2.trans (by norm_num [cell13072])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13072

/-! Source-cell containment and simple scalar guards at 13072. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13072)
open BstLean.Part268 (cell13072)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13072 ⟨10,by decide⟩).lower ∧ (cell13072 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13072 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13072 ⟨11,by decide⟩).lower ∧ (cell13072 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13072 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13072 ⟨12,by decide⟩).lower ∧ (cell13072 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13072 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13072 ⟨13,by decide⟩).lower ∧ (cell13072 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13072 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13072 ⟨14,by decide⟩).lower ∧ (cell13072 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13072 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13072 ⟨15,by decide⟩).lower ∧ (cell13072 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13072 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13072 ⟨16,by decide⟩).lower ∧ (cell13072 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13072 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13072 ⟨17,by decide⟩).lower ∧ (cell13072 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13072 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13072 ⟨18,by decide⟩).lower ∧ (cell13072 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13072 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13072 ⟨19,by decide⟩).lower ∧ (cell13072 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13072 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13072 ⟨20,by decide⟩).lower ∧ (cell13072 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13072 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13072 ⟨21,by decide⟩).lower ∧ (cell13072 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13072 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13072 ⟨22,by decide⟩).lower ∧ (cell13072 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13072 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13072 ⟨23,by decide⟩).lower ∧ (cell13072 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13072 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13072 ⟨24,by decide⟩).lower ∧ (cell13072 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13072 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13072 ⟨25,by decide⟩).lower ∧ (cell13072 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13072 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13072 ⟨26,by decide⟩).lower ∧ (cell13072 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13072 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13072 ⟨27,by decide⟩).lower ∧ (cell13072 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13072 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13072 ⟨28,by decide⟩).lower ∧ (cell13072 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13072 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13072 ⟨29,by decide⟩).lower ∧ (cell13072 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13072 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13072 ⟨30,by decide⟩).lower ∧ (cell13072 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13072 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13072 ⟨31,by decide⟩).lower ∧ (cell13072 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13072 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13072 ⟨32,by decide⟩).lower ∧ (cell13072 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13072 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13072 ⟨33,by decide⟩).lower ∧ (cell13072 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13072 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13072 ⟨34,by decide⟩).lower ∧ (cell13072 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13072 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13072 ⟨35,by decide⟩).lower ∧ (cell13072 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13072 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13072 ⟨36,by decide⟩).lower ∧ (cell13072 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13072 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13072 ⟨37,by decide⟩).lower ∧ (cell13072 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13072 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13072 ⟨38,by decide⟩).lower ∧ (cell13072 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13072 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13072 ⟨39,by decide⟩).lower ∧ (cell13072 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13072 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13072 ⟨40,by decide⟩).lower ∧ (cell13072 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13072 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13072 ⟨41,by decide⟩).lower ∧ (cell13072 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13072 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13072 ⟨42,by decide⟩).lower ∧ (cell13072 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13072 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13072 ⟨43,by decide⟩).lower ∧ (cell13072 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13072 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13072 ⟨44,by decide⟩).lower ∧ (cell13072 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13072 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13072 ⟨45,by decide⟩).lower ∧ (cell13072 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13072 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13072 ⟨46,by decide⟩).lower ∧ (cell13072 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13072 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13072 ⟨47,by decide⟩).lower ∧ (cell13072 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13072 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13072 ⟨48,by decide⟩).lower ∧ (cell13072 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13072 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13072 ⟨49,by decide⟩).lower ∧ (cell13072 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13072 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13072 ⟨50,by decide⟩).lower ∧ (cell13072 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13072 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13072 ⟨51,by decide⟩).lower ∧ (cell13072 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13072 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13072 ⟨52,by decide⟩).lower ∧ (cell13072 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13072 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13072 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13072 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13072,cell13072,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13072 i).lower ∧
    (cell13072 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13072 i).upper ≤ (0.532 : ℝ) ∧
    (cell13072 i).centre ≤ (0.1 : ℝ) ∧ (cell13072 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13072 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13072 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13072

/-! The local source numeric instances at 13072 have no network premises. -/
namespace BstLean.Part269.N13072
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13072)
open BstLean.Part268 (cell13072)

noncomputable def sourceNumerics13072 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13072 (cell13072 i)
      scalarRow13072.M scalarRow13072.H scalarRow13072.xi := by
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
    energy_allowance := scalarRow13072.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13072]
    centre_nonneg := (scalarRow13072.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13072])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13072
/-! Actual 13073 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13073 ≤ (1.035290207462 : ℝ) := by
  have hr : (114.337220536446 : ℝ) ≤ √(13073 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.337220536446 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13073 13073 (11 / 1000) ≤
    (0.008360242796 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13073) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.337220536446 : ℝ) ≤ √(13073 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13073)
  have hdiv : K / √(13073 : ℝ) ≤ K / 114.337220536446 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.337220536446 ≤ (0.008360242796 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13073.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13073 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13073 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13073 := gPlus_lower 13073
end BstLean.Part269.N13073

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13073
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035290207461 : ℝ) ≤ wn 13073 := by
  have hn : √(13073 : ℝ) ≤ 114.337220536447 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13073 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.337220536447 ≤ 2 / √(13073 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244571573 : ℝ) ≤ rhoBar 13073 BstLean.Part154.csC ∧
    rhoBar 13073 BstLean.Part154.csC ≤ 0.000244571951 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035290207461 : ℝ) / (1.295212 * 13073) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035290207462 : ℝ) / (1.29521 * 13073) := by gcongr
      _ ≤ (0.000244571951 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13073 BstLean.Part154.csC) ≤ 0.000978347620 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13073 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) ≤ 0.000186805454 ∧
    cc1 (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) ≤ 0.000118865603 ∧
    cc2 (rhoBar 13073 BstLean.Part154.csC) ≤ 0.000069002456 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13073 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13073 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13073 BstLean.Part154.csC * nuR (rhoBar 13073 BstLean.Part154.csC)) ≤ 0.000489158856 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244571951 : ℝ) * 0.000978347620 := by gcongr
      _ ≤ (0.000489158856 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13073 BstLean.Part154.csC) * nuR (rhoBar 13073 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978347620 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13073 BstLean.Part154.csC) * rhoBar 13073 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244571951 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244571951 / 2 + 0.399 * 0.000978347620 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186805454 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489158856 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118865603 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244571951 / 1.414213562 := by gcongr
      _ ≤ (0.000069002456 : ℝ) := by norm_num

end BstLean.Part269.N13073

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13073
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) ≤ 1.50701E-7 := by
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13073 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13073 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13073 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186805454 : ℝ) ^ 2 + 0.000118865603 ^ 2 + 3 * 0.000069002456 ^ 2 +
        2 * 0.797885 * 0.000186805454 * 0.000118865603 + 2 * 0.000186805454 * 0.000069002456 +
        4 * 0.797885 * 0.000118865603 * 0.000069002456 := by gcongr
    _ ≤ (1.50701E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13073 BstLean.Part154.csC Θ ≤ 0.002551715519 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13073 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13073 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13073 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035290207462 * 1.50701E-7 / (0.000244571573 : ℝ) := by gcongr
    _ ≤ 0.002551715519 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13073 BstLean.Part154.csC Θ ≤ 0.002829836971 + 0.000644776142 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13073 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13073 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035290207462 : ℝ) * ((2 * Θ * 0.000244571951 +
        (6863 / 10000) * 0.000244571951 * 13073 * 0.000978347620) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002829836971 + 0.000644776142 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13073 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13073 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13073 0.011 Θ ∧ gammaRatio 13073 0.011 Θ ≤ 0.000084077513 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13073 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035290207462 : ℝ) * 0.525 / ((1 - 0.011) * 13073) := by gcongr
      _ ≤ (0.000084077513 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13073 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13073 0.011 Θ) :=
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
    badAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13073 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13073 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13073 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13073 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13073 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13073 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13073 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13073 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13073 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13073 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035290207462 : ℝ) * 13073 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003213586358 + 0.003196491661 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13073

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13073
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13073 BstLean.Part154.csC) (piBar (rhoBar 13073 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13073 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13073 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13073 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13073 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13073 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13073 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13073 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13073 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13073 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13073 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051722090650 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13073) ≤ 0.010444871543 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13073 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035290207462)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010444871543 + 2 * 0.737676 / 13073) := by gcongr
    _ ≤ (0.051722090650 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13073 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13073

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13073
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519955174 : ℝ) ≤ plow 13073 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13073) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398344481)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339650648) : eMP 13073 0.011 xi bn ≤ 0.001153809000 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13073 : ℝ) * (1 - 0.011))) ≤ 0.000570538510 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339650648 / (13073 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570538510 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570538510 : ℝ) + 3.141593 * 0.052398344481 / (13073 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153809000 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398344481)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339650648) : PiBarMP 13073 12 0.011 xi bn ≤ 0.158911339419 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13073 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036601238340 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.706626895709 : ℝ) ≤ √((13073 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.337220536446 : ℝ) ≤ √(13073 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13073) ≤ 0.121853655331 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036601238340 + 0.052398344481 * 1.772454 / (2 * (113.706626895709 : ℝ))) * (1 + 0.001153809000) +
        8 / (13073 * 114.337220536446) + 0.121853655331 := by gcongr
    _ ≤ (0.158911339419 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398344481)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339650648) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280628937383) :
    parallelOracle 13073 0.011 xi bn cd ≤ 0.159873665873 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13073 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13073 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519955174 : ℝ) ≤ plow 13073 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.337220536446 : ℝ) ≤ √(13073 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280628937383 : ℝ) / (2 * 0.560519955174 * 114.337220536446)) * 0.158911339419 +
        0.280628937383 ^ 2 / (2 * 0.560519955174 * 114.337220536446) := by gcongr
    _ ≤ (0.159873665873 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052398344481) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339650648)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280628937383) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13073 13073 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519955174 : ℝ) ≤ plow 13073 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.337220536446 : ℝ) ≤ √(13073 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13073 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13073 Θ 1.22 ≤ 0.011598152324 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.337220536446 := by gcongr <;> linarith
      _ ≤ (0.011598152324 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13073 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13073 13073 0.011 ≤ 0.008360242796 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13073 13073 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13073 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13073 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13073 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13073 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159873665873 + 0.011598152324 + (0.008360242796 : ℝ) *
        (1 + 2 * (0.280628937383 + 0.011598152324) / (0.560519955174 * 114.337220536446))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13073]

end BstLean.Part269.N13073

/-! The original eight local profiles supply actual 13073 moment certificates. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13073 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052398344481 ∧
    0 ≤ bN 13073 BstLean.Part154.csC (groupTheta g) ∧ bN 13073 BstLean.Part154.csC (groupTheta g) ≤ 0.001339650648 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13073 13073 0.011
      (momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13073 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13073 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13073 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228906846733 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13073 0.011
      (momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13073 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13073
/-! The actual computed-centre upper energy formula at 13073. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13073

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13073)
open BstLean.Part268 (cell13073)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084471060438
  | 2 => 0.085397284453
  | 3 => 0.086319351309
  | 4 => 0.087238139170
  | 5 => 0.088154725824
  | 6 => 0.089070420244
  | 7 => 0.089986797492
  | 8 => 0.090905737065
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13073 13073 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13073 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13073

/-! Actual upper energy certificates on all 43 source endpoints at 13073. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13073)
open BstLean.Part268 (cell13073)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13073 (gMinus 13073) (1 - (cell13073 i).lower) ≤ 1 ∧
    energyUpper 13073 (gMinus 13073) (BstLean.Part211.gPlus 13073)
      (finiteEnergy 13073 13073 0.011) (1 - (cell13073 i).lower) ≤
      (cell13073 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨10,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨11,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨12,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨13,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨14,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨15,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨16,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨17,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨18,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨19,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨20,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨21,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨22,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨23,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨24,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨25,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨26,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨27,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨28,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨29,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨30,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨31,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨32,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨33,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨34,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨35,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨36,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨37,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨38,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨39,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨40,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨41,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨42,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨43,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨44,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨45,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨46,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨47,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨48,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨49,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨50,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨51,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13073) (by norm_num)
        (q := 1 - (cell13073 ⟨52,by decide⟩).lower)
        (by norm_num [cell13073]) (by norm_num [cell13073])
      exact ⟨E.1,E.2.trans (by norm_num [cell13073])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13073

/-! Source-cell containment and simple scalar guards at 13073. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13073)
open BstLean.Part268 (cell13073)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13073 ⟨10,by decide⟩).lower ∧ (cell13073 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13073 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13073 ⟨11,by decide⟩).lower ∧ (cell13073 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13073 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13073 ⟨12,by decide⟩).lower ∧ (cell13073 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13073 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13073 ⟨13,by decide⟩).lower ∧ (cell13073 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13073 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13073 ⟨14,by decide⟩).lower ∧ (cell13073 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13073 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13073 ⟨15,by decide⟩).lower ∧ (cell13073 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13073 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13073 ⟨16,by decide⟩).lower ∧ (cell13073 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13073 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13073 ⟨17,by decide⟩).lower ∧ (cell13073 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13073 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13073 ⟨18,by decide⟩).lower ∧ (cell13073 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13073 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13073 ⟨19,by decide⟩).lower ∧ (cell13073 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13073 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13073 ⟨20,by decide⟩).lower ∧ (cell13073 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13073 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13073 ⟨21,by decide⟩).lower ∧ (cell13073 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13073 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13073 ⟨22,by decide⟩).lower ∧ (cell13073 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13073 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13073 ⟨23,by decide⟩).lower ∧ (cell13073 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13073 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13073 ⟨24,by decide⟩).lower ∧ (cell13073 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13073 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13073 ⟨25,by decide⟩).lower ∧ (cell13073 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13073 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13073 ⟨26,by decide⟩).lower ∧ (cell13073 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13073 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13073 ⟨27,by decide⟩).lower ∧ (cell13073 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13073 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13073 ⟨28,by decide⟩).lower ∧ (cell13073 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13073 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13073 ⟨29,by decide⟩).lower ∧ (cell13073 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13073 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13073 ⟨30,by decide⟩).lower ∧ (cell13073 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13073 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13073 ⟨31,by decide⟩).lower ∧ (cell13073 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13073 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13073 ⟨32,by decide⟩).lower ∧ (cell13073 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13073 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13073 ⟨33,by decide⟩).lower ∧ (cell13073 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13073 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13073 ⟨34,by decide⟩).lower ∧ (cell13073 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13073 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13073 ⟨35,by decide⟩).lower ∧ (cell13073 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13073 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13073 ⟨36,by decide⟩).lower ∧ (cell13073 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13073 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13073 ⟨37,by decide⟩).lower ∧ (cell13073 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13073 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13073 ⟨38,by decide⟩).lower ∧ (cell13073 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13073 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13073 ⟨39,by decide⟩).lower ∧ (cell13073 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13073 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13073 ⟨40,by decide⟩).lower ∧ (cell13073 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13073 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13073 ⟨41,by decide⟩).lower ∧ (cell13073 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13073 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13073 ⟨42,by decide⟩).lower ∧ (cell13073 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13073 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13073 ⟨43,by decide⟩).lower ∧ (cell13073 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13073 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13073 ⟨44,by decide⟩).lower ∧ (cell13073 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13073 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13073 ⟨45,by decide⟩).lower ∧ (cell13073 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13073 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13073 ⟨46,by decide⟩).lower ∧ (cell13073 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13073 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13073 ⟨47,by decide⟩).lower ∧ (cell13073 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13073 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13073 ⟨48,by decide⟩).lower ∧ (cell13073 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13073 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13073 ⟨49,by decide⟩).lower ∧ (cell13073 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13073 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13073 ⟨50,by decide⟩).lower ∧ (cell13073 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13073 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13073 ⟨51,by decide⟩).lower ∧ (cell13073 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13073 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13073 ⟨52,by decide⟩).lower ∧ (cell13073 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13073 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13073 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13073 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13073,cell13073,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13073 i).lower ∧
    (cell13073 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13073 i).upper ≤ (0.532 : ℝ) ∧
    (cell13073 i).centre ≤ (0.1 : ℝ) ∧ (cell13073 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13073 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13073 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13073

/-! The local source numeric instances at 13073 have no network premises. -/
namespace BstLean.Part269.N13073
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13073)
open BstLean.Part268 (cell13073)

noncomputable def sourceNumerics13073 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13073 (cell13073 i)
      scalarRow13073.M scalarRow13073.H scalarRow13073.xi := by
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
    energy_allowance := scalarRow13073.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13073]
    centre_nonneg := (scalarRow13073.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13073])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13073
/-! Actual 13074 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13074 ≤ (1.035288846102 : ℝ) := by
  have hr : (114.341593481987 : ℝ) ≤ √(13074 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.341593481987 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13074 13074 (11 / 1000) ≤
    (0.008359923059 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13074) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.341593481987 : ℝ) ≤ √(13074 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13074)
  have hdiv : K / √(13074 : ℝ) ≤ K / 114.341593481987 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.341593481987 ≤ (0.008359923059 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13074.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13074 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13074 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13074 := gPlus_lower 13074
end BstLean.Part269.N13074

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13074
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035288846101 : ℝ) ≤ wn 13074 := by
  have hn : √(13074 : ℝ) ≤ 114.341593481988 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13074 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.341593481988 ≤ 2 / √(13074 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244552544 : ℝ) ≤ rhoBar 13074 BstLean.Part154.csC ∧
    rhoBar 13074 BstLean.Part154.csC ≤ 0.000244552923 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035288846101 : ℝ) / (1.295212 * 13074) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035288846102 : ℝ) / (1.29521 * 13074) := by gcongr
      _ ≤ (0.000244552923 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13074 BstLean.Part154.csC) ≤ 0.000978271499 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13074 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) ≤ 0.000186790920 ∧
    cc1 (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) ≤ 0.000118856354 ∧
    cc2 (rhoBar 13074 BstLean.Part154.csC) ≤ 0.000068997088 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13074 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13074 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13074 BstLean.Part154.csC * nuR (rhoBar 13074 BstLean.Part154.csC)) ≤ 0.000489120798 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244552923 : ℝ) * 0.000978271499 := by gcongr
      _ ≤ (0.000489120798 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13074 BstLean.Part154.csC) * nuR (rhoBar 13074 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978271499 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13074 BstLean.Part154.csC) * rhoBar 13074 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244552923 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244552923 / 2 + 0.399 * 0.000978271499 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186790920 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489120798 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118856354 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244552923 / 1.414213562 := by gcongr
      _ ≤ (0.000068997088 : ℝ) := by norm_num

end BstLean.Part269.N13074

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13074
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) ≤ 1.50677E-7 := by
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13074 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13074 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13074 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186790920 : ℝ) ^ 2 + 0.000118856354 ^ 2 + 3 * 0.000068997088 ^ 2 +
        2 * 0.797885 * 0.000186790920 * 0.000118856354 + 2 * 0.000186790920 * 0.000068997088 +
        4 * 0.797885 * 0.000118856354 * 0.000068997088 := by gcongr
    _ ≤ (1.50677E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13074 BstLean.Part154.csC Θ ≤ 0.002551504310 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13074 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13074 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13074 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035288846102 * 1.50677E-7 / (0.000244552544 : ℝ) := by gcongr
    _ ≤ 0.002551504310 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13074 BstLean.Part154.csC Θ ≤ 0.002829609355 + 0.000644725130 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13074 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13074 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035288846102 : ℝ) * ((2 * Θ * 0.000244552923 +
        (6863 / 10000) * 0.000244552923 * 13074 * 0.000978271499) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002829609355 + 0.000644725130 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13074 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13074 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13074 0.011 Θ ∧ gammaRatio 13074 0.011 Θ ≤ 0.000084070971 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13074 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035288846102 : ℝ) * 0.525 / ((1 - 0.011) * 13074) := by gcongr
      _ ≤ (0.000084070971 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13074 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13074 0.011 Θ) :=
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
    badAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000383749387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13074 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13074 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13074 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13074 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13074 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13074 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13074 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13074 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13074 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13074 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035288846102 : ℝ) * 13074 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000383749387 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003213358742 + 0.003196229440 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13074

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13074
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13074 BstLean.Part154.csC) (piBar (rhoBar 13074 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13074 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13074 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13074 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13074 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13074 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13074 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13074 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13074 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13074 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13074 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051720091420 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13074) ≤ 0.010444472084 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13074 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035288846102)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010444472084 + 2 * 0.737676 / 13074) := by gcongr
    _ ≤ (0.051720091420 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13074 12 ≤ 0.0015 := by
  exact BstLean.Part269.S28.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13074

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13074
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560519997850 : ℝ) ≤ plow 13074 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13074) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052397979198)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339539763) : eMP 13074 0.011 xi bn ≤ 0.001153717073 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13074 : ℝ) * (1 - 0.011))) ≤ 0.000570493078 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339539763 / (13074 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570493078 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570493078 : ℝ) + 3.141593 * 0.052397979198 / (13074 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153717073 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052397979198)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339539763) : PiBarMP 13074 12 0.011 xi bn ≤ 0.158905140125 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13074 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036599723538 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.710975723542 : ℝ) ≤ √((13074 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.341593481987 : ℝ) ≤ √(13074 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13074) ≤ 0.121848995090 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036599723538 + 0.052397979198 * 1.772454 / (2 * (113.710975723542 : ℝ))) * (1 + 0.001153717073) +
        8 / (13074 * 114.341593481987) + 0.121848995090 := by gcongr
    _ ≤ (0.158905140125 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052397979198)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339539763) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280626140266) :
    parallelOracle 13074 0.011 xi bn cd ≤ 0.159867400415 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13074 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13074 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560519997850 : ℝ) ≤ plow 13074 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.341593481987 : ℝ) ≤ √(13074 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280626140266 : ℝ) / (2 * 0.560519997850 * 114.341593481987)) * 0.158905140125 +
        0.280626140266 ^ 2 / (2 * 0.560519997850 * 114.341593481987) := by gcongr
    _ ≤ (0.159867400415 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052397979198) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339539763)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280626140266) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13074 13074 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560519997850 : ℝ) ≤ plow 13074 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.341593481987 : ℝ) ≤ √(13074 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13074 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13074 Θ 1.22 ≤ 0.011597708757 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.341593481987 := by gcongr <;> linarith
      _ ≤ (0.011597708757 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13074 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13074 13074 0.011 ≤ 0.008359923059 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13074 13074 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13074 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13074 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13074 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13074 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159867400415 + 0.011597708757 + (0.008359923059 : ℝ) *
        (1 + 2 * (0.280626140266 + 0.011597708757) / (0.560519997850 * 114.341593481987))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13074]

end BstLean.Part269.N13074

/-! The original eight local profiles supply actual 13074 moment certificates. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13074 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052397979198 ∧
    0 ≤ bN 13074 BstLean.Part154.csC (groupTheta g) ∧ bN 13074 BstLean.Part154.csC (groupTheta g) ≤ 0.001339539763 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13074 13074 0.011
      (momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13074 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13074 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13074 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228906048846 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13074 0.011
      (momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13074 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13074
/-! The actual computed-centre upper energy formula at 13074. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13074

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13074)
open BstLean.Part268 (cell13074)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084468499224
  | 2 => 0.085394690679
  | 3 => 0.086316720197
  | 4 => 0.087235464812
  | 5 => 0.088152000974
  | 6 => 0.089067636078
  | 7 => 0.089983943346
  | 8 => 0.090902800136
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13074 13074 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13074 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003218831707 + 0.003202305177 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S28.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S28.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13074

/-! Actual upper energy certificates on all 43 source endpoints at 13074. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13074)
open BstLean.Part268 (cell13074)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13074 (gMinus 13074) (1 - (cell13074 i).lower) ≤ 1 ∧
    energyUpper 13074 (gMinus 13074) (BstLean.Part211.gPlus 13074)
      (finiteEnergy 13074 13074 0.011) (1 - (cell13074 i).lower) ≤
      (cell13074 i).energy := by
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
      have E := BstLean.Part269.S28.uniformEnergy10 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨10,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy11 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨11,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy12 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨12,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy13 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨13,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy14 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨14,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy15 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨15,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy16 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨16,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy17 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨17,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy18 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨18,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy19 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨19,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy20 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨20,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy21 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨21,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy22 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨22,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy23 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨23,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy24 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨24,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy25 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨25,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy26 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨26,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy27 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨27,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy28 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨28,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy29 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨29,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy30 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨30,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy31 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨31,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy32 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨32,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy33 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨33,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy34 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨34,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy35 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨35,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy36 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨36,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy37 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨37,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy38 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨38,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy39 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨39,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy40 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨40,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy41 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨41,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy42 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨42,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy43 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨43,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy44 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨44,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy45 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨45,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy46 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨46,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy47 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨47,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy48 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨48,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy49 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨49,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy50 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨50,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy51 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨51,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S28.uniformEnergy52 (n := 13074) (by norm_num)
        (q := 1 - (cell13074 ⟨52,by decide⟩).lower)
        (by norm_num [cell13074]) (by norm_num [cell13074])
      exact ⟨E.1,E.2.trans (by norm_num [cell13074])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13074

/-! Source-cell containment and simple scalar guards at 13074. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13074)
open BstLean.Part268 (cell13074)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13074 ⟨10,by decide⟩).lower ∧ (cell13074 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13074 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13074 ⟨11,by decide⟩).lower ∧ (cell13074 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13074 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13074 ⟨12,by decide⟩).lower ∧ (cell13074 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13074 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13074 ⟨13,by decide⟩).lower ∧ (cell13074 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13074 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13074 ⟨14,by decide⟩).lower ∧ (cell13074 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13074 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13074 ⟨15,by decide⟩).lower ∧ (cell13074 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13074 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13074 ⟨16,by decide⟩).lower ∧ (cell13074 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13074 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13074 ⟨17,by decide⟩).lower ∧ (cell13074 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13074 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13074 ⟨18,by decide⟩).lower ∧ (cell13074 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13074 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13074 ⟨19,by decide⟩).lower ∧ (cell13074 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13074 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13074 ⟨20,by decide⟩).lower ∧ (cell13074 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13074 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13074 ⟨21,by decide⟩).lower ∧ (cell13074 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13074 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13074 ⟨22,by decide⟩).lower ∧ (cell13074 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13074 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13074 ⟨23,by decide⟩).lower ∧ (cell13074 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13074 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13074 ⟨24,by decide⟩).lower ∧ (cell13074 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13074 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13074 ⟨25,by decide⟩).lower ∧ (cell13074 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13074 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13074 ⟨26,by decide⟩).lower ∧ (cell13074 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13074 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13074 ⟨27,by decide⟩).lower ∧ (cell13074 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13074 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13074 ⟨28,by decide⟩).lower ∧ (cell13074 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13074 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13074 ⟨29,by decide⟩).lower ∧ (cell13074 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13074 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13074 ⟨30,by decide⟩).lower ∧ (cell13074 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13074 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13074 ⟨31,by decide⟩).lower ∧ (cell13074 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13074 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13074 ⟨32,by decide⟩).lower ∧ (cell13074 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13074 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13074 ⟨33,by decide⟩).lower ∧ (cell13074 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13074 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13074 ⟨34,by decide⟩).lower ∧ (cell13074 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13074 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13074 ⟨35,by decide⟩).lower ∧ (cell13074 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13074 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13074 ⟨36,by decide⟩).lower ∧ (cell13074 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13074 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13074 ⟨37,by decide⟩).lower ∧ (cell13074 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13074 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13074 ⟨38,by decide⟩).lower ∧ (cell13074 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13074 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13074 ⟨39,by decide⟩).lower ∧ (cell13074 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13074 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13074 ⟨40,by decide⟩).lower ∧ (cell13074 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13074 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13074 ⟨41,by decide⟩).lower ∧ (cell13074 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13074 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13074 ⟨42,by decide⟩).lower ∧ (cell13074 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13074 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13074 ⟨43,by decide⟩).lower ∧ (cell13074 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13074 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13074 ⟨44,by decide⟩).lower ∧ (cell13074 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13074 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13074 ⟨45,by decide⟩).lower ∧ (cell13074 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13074 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13074 ⟨46,by decide⟩).lower ∧ (cell13074 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13074 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13074 ⟨47,by decide⟩).lower ∧ (cell13074 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13074 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13074 ⟨48,by decide⟩).lower ∧ (cell13074 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13074 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13074 ⟨49,by decide⟩).lower ∧ (cell13074 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13074 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13074 ⟨50,by decide⟩).lower ∧ (cell13074 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13074 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13074 ⟨51,by decide⟩).lower ∧ (cell13074 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13074 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13074 ⟨52,by decide⟩).lower ∧ (cell13074 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13074 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13074 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13074 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13074,cell13074,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13074 i).lower ∧
    (cell13074 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13074 i).upper ≤ (0.532 : ℝ) ∧
    (cell13074 i).centre ≤ (0.1 : ℝ) ∧ (cell13074 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13074 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13074 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13074

/-! The local source numeric instances at 13074 have no network premises. -/
namespace BstLean.Part269.N13074
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13074)
open BstLean.Part268 (cell13074)

noncomputable def sourceNumerics13074 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13074 (cell13074 i)
      scalarRow13074.M scalarRow13074.H scalarRow13074.xi := by
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
    energy_allowance := scalarRow13074.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13074]
    centre_nonneg := (scalarRow13074.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D28.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13074])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13074